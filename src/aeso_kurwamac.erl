-module(aeso_kurwamac).
-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").
-define(DBG(A, B), ?debugFmt(A, B)).
-define(DBG(A), ?debugMsg(A)).

%% Liquid type variable
-type ltvar() :: {ltvar, string()}.

%% Substitution of a variable with an expression
-type subst() :: {string(), aeso_syntax:expr()}.

-type predicate() :: aeso_syntax:predicate().

-type template() :: aeso_syntax:dep_type( predicate()
                                        | {template, [subst()], ltvar()}).

-record(type_env,
        { type_binds :: maps:map(string(), aeso_syntax:liquid_type())
        , path_pred :: predicate()
        }).
-type type_env() :: #type_env{}.

-type constr() :: {subtype, type_env(), template(), template()}
                | {well_formed, type_env(), template()}.

%% Grouped subtype
-type subtype_constr() :: {subtype, [{type_env(), subst(), template()}], ltvar()}.

-record(kinfo, {base :: aeso_syntax:type(), all_qs :: predicate(), curr_qs :: predicate()}).
-type kinfo() :: #kinfo{}.

%%%% INIT


init_refiner() ->
    put(ltvar_supply, 0),
    put(id_supply, 0),
    ok.


%%%% ENVIRONMENT

ann() -> [{origin, hagia}].

-spec init_type_env() -> type_env().
init_type_env() ->
    #type_env{
       type_binds = #{},
       path_pred = []
      }.

-spec fresh_ltvar(string()) -> ltvar().
fresh_ltvar(Name) ->
    I = get(ltvar_supply),
    put(ltvar_supply, I + 1),
    {ltvar, Name ++ "_" ++ integer_to_list(I)}.

-spec fresh_template(string()) -> template().
fresh_template(Name) -> {template, [], fresh_ltvar(Name)}.

get_var(#type_env{type_binds = TB}, Name) ->
    maps:get(Name, TB, undefined).


bind_var(Name, T, TEnv = #type_env{type_binds = TB}) ->
    TEnv#type_env{type_binds = maps:put(Name, T, TB)}.
bind_vars(L, Env) ->
    lists:foldl(
      fun({Name, T}, Env0) -> bind_var(Name, T, Env0) end,
      Env, L).

assert(L, Env = #type_env{path_pred = GP}) when is_list(L) ->
    Env#type_env{path_pred = L ++ GP};
assert(E, Env = #type_env{path_pred = GP}) ->
    Env#type_env{path_pred = [E|GP]}.

bind_args(Args, Env) ->
    lists:foldl(
      fun({{id, _, Name}, T}, Env0) -> bind_var(Name, T, Env0)
      end,
      Env, Args).


%%%% CONSTRAINT GENERATION


fresh_id(Name) ->
    I = get(id_supply),
    put(id_supply, I + 1),
    {id, [], Name ++ "_" ++ integer_to_list(I)}.

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
-define(op(A, Op, B), {app, [{format, infix}|ann()], {Op, ann()}, [A, B]}).
-define(op(Op, B), {app, [{format, prefix}|ann()], {Op, ann()}, [B]}).

constr_expr(Env, {typed, Ann, {app, Ann1, F, Args}, RetT}, S)
  when element(1, F) =/= typed ->
    ArgTypes = [ArgT || {typed, _, _, ArgT} <- Args],
    TypedF = {typed, Ann, F, {fun_t, Ann, ann(), ArgTypes, RetT}},
    constr_expr(Env, {typed, Ann, {app, Ann1, TypedF, Args}, RetT}, S);
constr_expr(Env, {typed, _, Expr, T}, S) ->
    constr_expr(Env, Expr, T, S);
constr_expr(_, X, _) ->
    error({todo, X}).

constr_expr(Env, Expr = {id, _, Name}, T, S) ->
    case get_var(Env, Name) of
        undefined ->
            Eq = ?op(nu, '==', Expr),
            {{refined_t, ann(), T, [Eq]}, S};
        {refined_t, Ann, B, _} ->
            Eq = ?op(nu, '==', Expr),
            {{refined_t, Ann, B, [Eq]}, S};
        T1 -> {T1, S}
    end;
constr_expr(_Env, I = {int, _, _}, T, S) ->
    {?refined(T, [?op(nu, '==', I)]), S};
constr_expr(_Env, {bool, _, B}, T, S) ->
    {?refined(T, [if B -> nu; true -> ?op('!', nu) end]), S};

constr_expr(_Env, Expr = {CmpOp, Ann}, {fun_t, _, _, [OpLT, OpRT], RetT = {id, _, "bool"}}, S)
      when CmpOp =:= '<' orelse
           CmpOp =:= '=<' orelse
           CmpOp =:= '>' orelse
           CmpOp =:= '>=' orelse
           CmpOp =:= '==' orelse
           CmpOp =:= '!=' ->
    OpLV = fresh_id("opl"),
    OpRV = fresh_id("opr"),
    { {dep_fun_t, Ann, ann(),
       [{OpLV, ?refined(OpLT, [])}, {OpLV, ?refined(OpRT, [])}],
       ?refined(RetT, [?op(nu, '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
      }
    , S
    };

constr_expr(Env, {app, _, F, Args}, _, S0) ->
    {ExprT = {dep_fun_t, _, _, ArgsFT, RetT}, S1} = constr_expr(Env, F, S0),
    {ArgsT, S1} = constr_exprs(Env, Args, S1),
    { apply_subst([{X, Expr} || {{X, _}, Expr} <- lists:zip(ArgsFT, Args)], RetT)
    , [{subtype, Env, ArgT, ArgFT} || {{_, ArgFT}, ArgT} <- lists:zip(ArgsFT, ArgsT)] ++
      [{well_formed, Env, ExprT} | S1]
    };
constr_expr(Env, {'if', _, Cond, Then, Else}, T, S0) ->
    ExprT = ?refined(T, fresh_template("if")),
    {_, S1} = constr_expr(Env, Cond, S0),
    {ThenT, S2} = constr_expr(assert(Cond, Env), Then, S1),
    {ElseT, S3} = constr_expr(assert({neg, Cond}, Env),Else, S2),
    { ExprT
    , [ {well_formed, Env, ExprT}
      , {subtype, assert(Cond, Env), ThenT, ExprT}
      , {subtype, assert(?op('!', Cond), Env), ElseT, ExprT}
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
    HC = simplify1(H),
    simplify(T, HC ++ Acc);
simplify([], Acc) ->
    filter_obvious(Acc).

simplify1(C = {subtype, Env0, SubT, SupT}) ->
    case {SubT, SupT} of
        { {dep_fun_t, _, _, ArgsSub, RetSub}
        , {dep_fun_t, _, _, ArgsSup, RetSup}
        } ->
            Contra =
                [ {subtype, Env0, ArgSupT, ArgSubT} %% contravariant!
                 || {{_, ArgSubT}, {_, ArgSupT}} <- lists:zip(ArgsSub, ArgsSup)
                ],
            Env1 = Env0#type_env{
                     type_binds =
                         maps:merge(maps:from_list([{Id, T} || {{id, _, Id}, T} <- ArgsSup]), Env0#type_env.type_binds)
                    },
            simplify([{subtype, Env1, RetSub, RetSup}|Contra]);
        _ -> [C]
    end;
simplify1(C = {well_formed, Env0, T}) ->
    case T of
        {dep_fun_t, _, _, Args, Ret} ->
            FromArgs =
                [ {well_formed, Env0, ArgT}
                  || {_, ArgT} <- Args
                ],
            Env1 = Env0#type_env{
                     type_binds =
                         maps:merge(maps:from_list([{Id, T1} || {{id, _, Id}, T1} <- Args]), Env0#type_env.type_binds)
                    },
            simplify([{well_formed, Env1, Ret}|FromArgs]);
        _ -> [C]
    end.

filter_obvious(L) ->
    filter_obvious(L, []).
filter_obvious([], Acc) ->
    Acc;
filter_obvious([H|T], Acc) ->
    case H of
        {well_formed, _, {refined_t, _, _, []}} ->
            filter_obvious(T, Acc);
         _ -> filter_obvious(T, [H|Acc])
    end.

int_qualifiers(Thing) ->
    [ ?op(nu, '=<', Thing)
    , ?op(nu, '>=', Thing)
    ].

init_assg(Cs) ->
    lists:foldl(
      fun({well_formed, CEnv, {refined_t, _, BaseT, {template, _, LV}}}, Acc) ->
              AllQs = inst_pred(maps:to_list(CEnv#type_env.type_binds)),
              Acc#{LV => #kinfo{base = BaseT, all_qs = AllQs, curr_qs = AllQs}};
         (_, Acc) -> Acc
      end, #{}, Cs).


inst_pred(Scope) ->
    Pred1 =
        [ Q
          || {Var, {refined_t, _, {id, _, "int"}, _}} <- Scope,
             Q <- int_qualifiers({id, ann(), Var})
        ],
    Pred1.

group_subtypes(Cs) ->
    Subts = [C || C = {subtype, _, _, {refined_t, _, _, {template, _, _}}} <- Cs],
    WFs = Cs -- Subts,

    SubtsMap =
        lists:foldl(
          fun ({subtype, Env, T, {refined_t, _, _, {template, Subst, LV}}}, Map) ->
                  maps:put(LV, [{Env, Subst, T}|maps:get(LV, Map, [])], Map)
          end, #{}, Subts
         ),
    WFs ++ [ {subtype, Ts, LV}
            || {LV, Ts} <- maps:to_list(SubtsMap)
           ].

assg_of(Assg, Var = {ltvar, _}) ->
    case maps:get(Var, Assg, undef) of
        undef ->
            #kinfo
                { base = {id, ann(), "int"} %% TODO NOT ONLY INT
                , all_qs  = []
                , curr_qs = []
                };
        A -> A
    end.

pred_of(Assg, Var = {ltvar, _}) ->
    (assg_of(Assg, Var))#kinfo.curr_qs;
pred_of(_, P) when is_list(P) ->
    P;
pred_of(Assg, {template, _, P}) ->
    pred_of(Assg, P);
pred_of(Assg, {refined_t, _, _, P}) ->
    pred_of(Assg, P).



solve(Cs) ->
    solve(init_assg(Cs), Cs, Cs).
solve(Assg, _, []) ->
    Assg;
solve(Assg, AllCs, [C|Rest]) ->
    case valid_in(C, Assg) of
        false -> ?DBG("CONSTR INVALID"), solve(weaken(C, Assg), AllCs, AllCs);
        true  -> ?DBG("CONSTR VALID"), solve(Assg, AllCs, Rest)
    end.

valid_in({well_formed, _, _}, _) ->
    ?DBG("CHECKING VALID FOR WF"),
    true; %% TODO
valid_in({subtype, Subs, SupPredVar}, Assg) ->
    KInfo = assg_of(Assg, SupPredVar),
    ?DBG("CHECKING VALID FOR SUB ~p", [SupPredVar]),
    lists:all(
      fun({#type_env{type_binds = Scope, path_pred = PathPred}, _Subst, SubKVar}) ->
              VarPred = pred_of(Assg, SubKVar),
              ScopePred = [], %% TODO
              SubPred = PathPred ++ VarPred ++ ScopePred,
              impl_holds(Scope, SubPred, KInfo#kinfo.curr_qs) %% FIXME all or curr?
      end,
      Subs
     );
valid_in({subtype, #type_env{type_binds = Scope, path_pred = PathPred},
          {refined_t, _, _, SubP}, {refined_t, _, _, SupP}}, Assg) ->
    ScopePred = [], %% TODO
    SubPred = PathPred ++ pred_of(Assg, SubP) ++ ScopePred,
    case impl_holds(Scope, SubPred, pred_of(Assg, SupP)) of
        true -> ok;
        false -> throw(contradict)
    end,
    true. %% TODO !!!!

weaken({subtype, Subs, SubPredVar}, Assg) ->
    ?DBG("**** WEAKENING SUB FOR ~p", [SubPredVar]),
    KInfo = assg_of(Assg, SubPredVar),
    Filtered =
        [ Q || Q <- KInfo#kinfo.curr_qs,
               lists:all(fun({CEnv, Subst, Sub}) ->
                                 ?DBG("CHECKING SUB"),
                                 Valid = subtype_implies(CEnv, Sub, apply_subst(Subst, Q), Assg),
                                 case Valid of
                                     true -> ?DBG("SUB VALID");
                                     false -> ?DBG("SUB INVALID")
                                 end,
                                 Valid
                         end, Subs)
        ],
    ?DBG("**** WEAKENED FROM ~p TO ~p", [length(KInfo#kinfo.curr_qs), length(Filtered)]),
    NewKInfo = KInfo#kinfo{
                 curr_qs = Filtered
                },
    Assg#{SubPredVar => NewKInfo}.

subtype_implies(#type_env{type_binds=Scope, path_pred=PathPred},
                {refined_t, _, _, Template}, Q, Assg
               ) ->
    SubPred =
        case Template of
            {template, _Subst, KVar} -> %% TODO seriously we don't give a shit about subst?
                (assg_of(Assg, KVar))#kinfo.curr_qs;
            P -> P
        end,
    ScopePred = [], %% TODO
    LPred = SubPred ++ ScopePred ++ PathPred,
    impl_holds(Scope, LPred, Q).


make_conjunction([]) -> {bool, ann(), true};
make_conjunction([H|T]) ->
    lists:foldl(
      fun (E, Acc) -> ?op(E, '&&', Acc)
      end, H, T);
make_conjunction(X) -> X.

impl_holds(Scope, Assump, Concl) ->
    ConclExpr  = make_conjunction(Concl),
    ?DBG("IMPL;\n* ASSUMPTION: ~s\n* CONCLUSION: ~s", [aeso_pretty:pp(expr, make_conjunction(Assump)), aeso_pretty:pp(expr, ConclExpr)]),
    aeso_smt:scoped(
      fun() ->
              [aeso_smt:declare_const({var, Var}, type_to_smt(T))
               || {Var, T} <- maps:to_list(Scope)
              ],
              aeso_smt:declare_const({var, "nu__"}, {var, "Int"}), %% FIXME
              [ aeso_smt:assert(expr_to_smt(Expr))
                || Expr <- Assump
              ],
              aeso_smt:assert(expr_to_smt(?op('!', ConclExpr))),
              not aeso_smt:check_sat()
      end).

type_to_smt({refined_t, _, T, _}) ->
    type_to_smt(T);
type_to_smt({id, _, "int"}) ->
    {var, "Int"};
type_to_smt(T) ->
    error({type_not_smtable, T}).

expr_to_smt({id, _, Var}) ->
    {var, Var};
expr_to_smt({bool, _, true}) ->
    {var, "true"};
expr_to_smt({bool, _, false}) ->
    {var, "false"};
expr_to_smt({int, _, I}) ->
    {int, I};
expr_to_smt({typed, _, E, _}) ->
    expr_to_smt(E);
expr_to_smt({app, _, F, Args}) ->
    {app, expr_to_smt(F), [expr_to_smt(Arg) || Arg <- Args]};
expr_to_smt({'&&', _}) -> "&&";
expr_to_smt({'||', _}) -> "||";
expr_to_smt({'=<', _}) -> "<=";
expr_to_smt({'>=', _}) -> ">=";
expr_to_smt({'==', _}) -> "=";
expr_to_smt({'<', _})  -> "<";
expr_to_smt({'>', _})  -> ">";
expr_to_smt({'+', _})  -> "+";
expr_to_smt({'-', _})  -> "-";
expr_to_smt({'*', _})  -> "*";
expr_to_smt({'/', _})  -> "div";
expr_to_smt({'!', _})  -> "not";
%% expr_to_smt(nu) -> error(nu_in_expr);
expr_to_smt(nu) -> {var, "nu__"};
expr_to_smt(E) -> error({not_smt_expr, E}).

