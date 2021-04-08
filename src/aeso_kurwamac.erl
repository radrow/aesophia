-module(aeso_kurwamac).
-compile([export_all, nowarn_export_all]).


%% Liquid type variable
-type ltvar() :: {ltvar, string()}.

%% Substitution of a variable with an expression
-type subst() :: {string(), aeso_syntax:expr()}.

-type predicate() :: aeso_syntax:predicate().

-type template() :: aeso_syntax:dep_type( predicate()
                                        | {template, [subst()], ltvar()}).


-record(env,
        { type_binds :: maps:map(string(), aeso_syntax:liquid_type())
        , assumptions :: predicate()
        }).
-type env() :: #env{}.

-type constr() :: {subtype, env(), template(), template()}
                | {well_formed, env(), template()}.

-type constr_idx() :: reference().

%% Grouped subtype
-type subtype_constr() :: {subtype, [{env(), template()}], ltvar()}.

-record(kinfo, {base :: aeso_syntax:type(), all_qs :: predicate(), curr_qs :: predicate()}).
-type kinfo() :: #kinfo{}.


%%%% INIT


init_refiner() ->
    put(ltvar_supply, 0),
    put(id_supply, 0).


%%%% ENVIRONMENT


init_env() ->
    #env{
       type_binds = #{},
       assumptions = []
      }.

fresh_ltvar(Name) ->
    I = get(ltvar_supply),
    put(ltvar_supply, I + 1),
    {ltvar, Name ++ "_" ++ integer_to_list(I)}.
fresh_template(Name) -> {template, [], fresh_ltvar(Name)}.

get_var(Env, Name) ->
    case maps:get(Name, Env, none) of
        none ->
            error({undef_var, Name});
        V -> V
    end.


bind_var(Name, T, Env = #env{type_binds = TB}) ->
    Env#env{type_binds = maps:put(Name, T, TB)}.
bind_vars(L, Env) ->
    lists:foldl(
      fun({Name, T}, Env0) -> bind_var(Name, T, Env0) end,
      Env, L).

assert(L, Env = #env{assumptions = GP}) when is_list(L) ->
    Env#env{assumptions = L ++ GP};
assert(E, Env = #env{assumptions = GP}) ->
    Env#env{assumptions = [E|GP]}.

bind_args(Args, Env) ->
    lists:foldl(
      fun({{id, _, Name}, T}, Env0) -> bind_var(Name, T, Env0)
      end,
      Env, Args).


%%%% CONSTRAINT GENERATION


fresh_id(Name) ->
    I = get(id_supply),
    put(id_supply, I + 1),
    {ltvar, Name ++ "_" ++ integer_to_list(I)}.

%% Decorates base types with templates through the AST
decorate_base_types(Type = {id, Ann, "int"}) ->
    {refined_t, Ann, Type, fresh_template("I")};
decorate_base_types(Type = {id, Ann, "bool"}) ->
    {refined_t, Ann, Type, fresh_template("B")};
decorate_base_types({fun_t, Ann, Named, Args, Ret}) ->
    { dep_fun_t, Ann, Named
    , [{fresh_id("arg"), decorate_base_types(Arg)}|| Arg <- Args]
    , decorate_base_types(Ret)
    };
decorate_base_types([]) -> [];
decorate_base_types([H|T]) -> [decorate_base_types(H)|decorate_base_types(T)];
decorate_base_types(T) when is_tuple(T) ->
    list_to_tuple(decorate_base_types(tuple_to_list(T)));
decorate_base_types(X) -> X.


constr_letfun(Env0, {letfun, Ann, _, Args, _, Body}, S) ->
    ArgsT =
        [ {ArgName, decorate_base_types(T)}
          || {typed, _, ArgName, T} <- Args
        ],
    Env1 = bind_args(ArgsT, Env0),
    {DepRetT, S1} = constr_expr(Env1, Body, S),
    DepSelfT =
        { dep_fun_t, Ann, []
        , ArgsT
        , DepRetT
        },

    {DepSelfT, S1}.


constr_exprs(Env, Es, S) ->
    constr_exprs(Env, Es, [], S).
constr_exprs(_, [], Acc, S) ->
    {lists:reverse(Acc), S};
constr_exprs(Env, [H|T], Acc, S0) ->
    {H1, S1} = constr_expr(Env, H, S0),
    constr_exprs(Env, T, [H1|Acc], S1).

-define(refined(T, Q), {refined_t, element(2, T), T, Q}).


constr_expr(Env, {typed, Ann, {app, Ann1, F, Args}, RetT}, S)
  when element(1, F) =/= typed ->
    ArgTypes = [ArgT || {typed, _, _, ArgT} <- Args],
    TypedF = {typed, Ann, F, {fun_t, Ann, [], ArgTypes, RetT}},
    constr_expr(Env, {typed, Ann, {app, Ann1, TypedF, Args}, RetT}, S);
constr_expr(Env, {typed, _, Expr, T}, S) ->
    constr_expr(Env, Expr, T, S);
constr_expr(_, X, _) ->
    error({todo, X}).

constr_expr(#env{type_binds = TB}, {id, _, Name}, T, S) ->
    case maps:get(Name, TB, undefined) of
        undefined -> {decorate_base_types(T), S};
        T1 -> {T1, S}
    end;
constr_expr(_Env, I = {int, _, _}, T, S) ->
    {?refined(T, [{app, [], {'==', []}, [nu, I]}]), S};
constr_expr(_Env, {bool, _, B}, T, S) ->
    {?refined(T, [if B -> nu; true -> {app, [], {'!', []}, [nu]} end]), S};

constr_expr(_Env, Expr = {CmpOp, Ann}, {fun_t, _, _, [OpLT, OpRT], RetT = {id, _, "bool"}}, S)
      when CmpOp =:= '<' orelse
           CmpOp =:= '=<' orelse
           CmpOp =:= '>' orelse
           CmpOp =:= '>=' orelse
           CmpOp =:= '==' orelse
           CmpOp =:= '!=' ->
    OpLV = fresh_id("opl"),
    OpRV = fresh_id("opr"),
    { {dep_fun_t, Ann, [],
       [{OpLV, ?refined(OpLT, [])}, {OpLV, ?refined(OpRT, [])}],
       ?refined(RetT, [{app, [], {'==', []}, [nu, {app, Ann, Expr, [OpLV, OpRV]}]}])
      }
    , S
    };

constr_expr(Env, {app, _, F, Args}, _, S0) ->
    {ExprT = {dep_fun_t, _, _, ArgsFT, RetT}, S1} = constr_expr(Env, F, S0),
    {ArgsT, S1} = constr_exprs(Env, Args, S1),
    { apply_subst([{X, Expr} || {{X, _}, Expr} <- lists:zip(ArgsFT, Args)], RetT)
    , [{subtype, Env, ArgT, ArgFT} || {{_, ArgFT}, ArgT} <- lists:zip(ArgsFT, ArgsT)]
      ++ [{well_formed, Env, ExprT} | S1]
    };
constr_expr(Env, {'if', _, Cond, Then, Else}, T, S0) ->
    ExprT = ?refined(T, fresh_template("if")),
    {_, S1} = constr_expr(Env, Cond, S0),
    {ThenT, S2} = constr_expr(assert(Cond, Env), Then, S1),
    {ElseT, S3} = constr_expr(assert({neg, Cond}, Env),Else, S2),
    { ExprT
    , [ {well_formed, Env, ExprT}
      , {subtype, assert(Cond, Env), ThenT, ExprT}
      , {subtype, assert({app, [], {'!', []}, [Cond]}, Env), ElseT, ExprT}
      | S3
      ]
    };
constr_expr(_, E, A, B) ->
    error({todo, E, A, B}).


%%%% Substitution

apply_subst1({id, _, X}, Expr, {id, _, X}) ->
    Expr;
apply_subst1(nu, Expr, nu) ->
    Expr;
apply_subst1(X, Expr, {template, S1, T}) ->
    {template, [{X, Expr}|S1], T};
apply_subst1(X, Expr, {refined_t, Ann, T, Qual}) ->
    {refined_t, Ann, T, apply_subst1(X, Expr, Qual)};
apply_subst1(X, Expr, {dep_fun_t, Ann, Named, Args, RetT}) ->
    {dep_fun_t, Ann, Named, apply_subst1(X, Expr, Args),
     case X of
         {id, _, Name} ->
             case [{} || {{id, _, ArgName}, _} <- Args, ArgName =:= Name] of
                 [] -> apply_subst1(X, Expr, RetT);
                 _ -> RetT
             end;
         _ -> apply_subst1(X, Expr, RetT)
     end
    };
apply_subst1(_X, _Expr, []) -> [];
apply_subst1(X, Expr, [H|T]) -> [apply_subst1(X, Expr, H)|apply_subst1(X, Expr, T)];
apply_subst1(X, Expr, T) when is_tuple(T) ->
    list_to_tuple(apply_subst1(X, Expr, tuple_to_list(T)));
apply_subst1(_X, _Expr, X) -> X.


apply_subst(Subs, Q) ->
    lists:foldl(fun({X, Expr}, Q0) -> apply_subst1(X, Expr, Q0) end, Q, Subs).


%% Solving

simplify(L) when is_list(L) ->
    simplify(L, []).
simplify([H|T], Acc) ->
    simplify(T, simplify1(H) ++ Acc);
simplify([], Acc) ->
    Acc.

simplify1(C = {subtype, Env, SubT, SupT}) ->
    case {SubT, SupT} of
        { {dep_fun_t, _, _, ArgsSub, RetSub}
        , {dep_fun_t, _, _, ArgsSup, RetSup}
        } ->
            Contra =
                [ {subtype, Env, ArgSupT, ArgSubT} %% contravariant!
                 || {{_, ArgSubT}, {_, ArgSupT}} <- lists:zip(ArgsSub, ArgsSup)
                ],
            Env1 = bind_args(ArgsSup, Env),
            simplify([{subtype, Env1, RetSub, RetSup}|Contra]);
        _ -> [C]
    end;
simplify1(C = {well_formed, Env, T}) ->
    case T of
        {dep_fun_t, _, _, Args, Ret} ->
            FromArgs =
                [ {well_formed, Env, ArgT}
                  || {_, ArgT} <- Args
                ],
            Env1 = bind_args(Args, Env),
            simplify([{well_formed, Env1, Ret}|FromArgs]);
        _ -> [C]
    end.
