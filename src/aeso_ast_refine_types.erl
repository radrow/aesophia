%%%-------------------------------------------------------------------
%%% @author Radosław Rowicki
%%% @doc
%%%     Liquid type checker for Sophia. Refines regular Sophia types
%%%     with dependent constraints and validates them.
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_ast_refine_types).

-compile([export_all]).

%% Substitution of a variable with an expression
-type subst() :: {string(), aeso_syntax:expr()}.


%% Liquid type variable
-type ltvar() :: {ltvar, reference()}.

-type template() :: aeso_syntax:dep_type( aeso_syntax:predicate()
                                        | {[subst()], ltvar()}).

-record(env,
       { type_binds :: maps:map(string(), aeso_syntax:liquid_type())
       , guard_preds :: aeso_syntax:predicate()
       }).
-type env() :: #env{}.

-type conclusion() :: {well_formed, template()} | {subtype, template(), template()}.
-type constr() :: {env(), conclusion()}.

env_typeof(Name, #env{type_binds = TB}) ->
    maps:get(Name, TB).

fresh_id() ->
    {id, [], erlang:ref_to_list(make_ref())}.
fresh_ltvar() -> {ltvar, make_ref()}.
fresh_template() -> {[], fresh_ltvar()}.

refine_types(AST) ->
    AST1 = decorate_base_types(AST).
    %% Cs = generate_constraints(env, AST1),
    %% solve_constraints(Cs).

%% Decorates base types with templates through the AST
decorate_base_types(Type = {id, Ann, "int"}) ->
    {refined_t, Ann, Type, fresh_template()};
decorate_base_types(Type = {id, Ann, "bool"}) ->
    {refined_t, Ann, Type, fresh_template()};
decorate_base_types({fun_t, Ann, Named, Args, Ret}) ->
    { dep_fun_t, Ann, Named
    , [{fresh_id(), decorate_base_types(Arg)}|| Arg <- Args]
    , decorate_base_types(Ret)
    };
decorate_base_types([]) -> [];
decorate_base_types([H|T]) -> [decorate_base_types(H)|decorate_base_types(T)];
decorate_base_types(T) when is_tuple(T) ->
    list_to_tuple(decorate_base_types(tuple_to_list(T)));
decorate_base_types(X) -> X.

bind_var(Name, T, Env = #env{type_binds = TB}) ->
    Env#env{type_binds = maps:put(Name, T, TB)}.
bind_vars(L, Env) ->
    lists:foldl(
      fun({Name, T}, Env0) -> bind_var(Name, T, Env0) end,
      Env, L).

assert(L, Env = #env{guard_preds = GP}) when is_list(L) ->
    Env#env{guard_preds = L ++ GP};
assert(E, Env = #env{guard_preds = GP}) ->
    Env#env{guard_preds = [E|GP]}.

bind_args(Args, Env) ->
    lists:foldl(
      fun({{id, _, Name}, T}, Env0) -> bind_var(Name, T, Env0)
      end,
      Env, Args).

empty_env() ->
    #env{type_binds = maps:new(), guard_preds = []}.

init_env() ->
    #env{
       type_binds =
           #{
           },
       guard_preds = []
      }.

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

-define(int, {id, [], "int"}).
-define(bool, {id, [], "bool"}).
-define(refined(A, B), {refined_t, [], A, B}).
-define(id(I), {id, [], I}).

constr_expr(Env, {typed, _, Expr, T}, S) ->
    constr_expr(Env, Expr, T, S);
constr_expr(_, {'<', Ann}, S) ->
    { {dep_fun_t, Ann, [],
       [{?id("opl"), ?refined(?int, [])}, {?id("opr"), ?refined(?int, [])}],
       ?refined(?bool, [{eq, nu, {lt, ?id("opl"), ?id("opr")}}])
      }
    , S
    };
constr_expr(_, X, _) ->
    error({todo, X}).

constr_expr(#env{type_binds = TB}, {id, _, Name}, T, S) ->
    case maps:get(Name, TB, undefined) of
        undefined -> {decorate_base_types(T), S};
        T1 -> {T1, S}
    end;
constr_expr(_Env, {int, _, _}, T, S) ->
    {T, S};
constr_expr(Env, {app, _, F, Args}, _, S0) ->
    {ExprT = {dep_fun_t, _, _, ArgsFT, RetT}, S1} = constr_expr(Env, F, S0),
    {ArgsT, S1} = constr_exprs(Env, Args, S1),
    { subst([{X, Expr} || {{X, _}, Expr} <- lists:zip(ArgsFT, Args)], RetT)
    , [{Env, {subtype, ArgT, ArgFT}} || {{_, ArgFT}, ArgT} <- lists:zip(ArgsFT, ArgsT)]
      ++ [{Env, {well_formed, ExprT}} | S1]
    };
constr_expr(Env, {'if', _, Cond, Then, Else}, T, S0) ->
    CondP = format_pred(Cond),
    ExprT = ?refined(T, fresh_template()),
    {_, S1} = constr_expr(Env, Cond, S0),
    {ThenT, S2} = constr_expr(assert(CondP, Env), Then, S1),
    {ElseT, S3} = constr_expr(assert({neg, CondP}, Env),Else, S2),
    { ExprT
    , [ {Env, {well_formed, ExprT}}
      , {assert(CondP, Env), {subtype, ThenT, ExprT}}
      , {assert({neg, CondP}, Env), {subtype, ElseT, ExprT}}
      | S3
      ]
    };
constr_expr(_, E, _, _) ->
    error({todo, E}).

subst(Subs, Q) ->
    lists:foldl(fun({X, Expr}, Q0) -> subst1(X, Expr, Q0) end, Q, Subs).

subst1({id, _, X}, Expr, {id, _, X}) ->
    Expr;
subst1(nu, Expr, nu) ->
    Expr;
subst1(X, Expr, {refined_t, Ann, T, Qual}) ->
    {refined_t, Ann, T, subst1(X, Expr, Qual)};
subst1(X, Expr, {dep_fun_t, Ann, Named, Args, RetT}) ->
    {dep_fun_t, Ann, Named, subst1(X, Expr, Args), subst1(X, Expr, RetT)};
subst1(X, Expr, [H|T]) ->
    [subst1(X, Expr, H)|subst1(X, Expr, T)];
subst1(X, Expr, {eq, A, B}) ->
    {eq, subst1(X, Expr, A), subst1(X, Expr, B)};
subst1(X, Expr, {lt, A, B}) ->
    {lt, subst1(X, Expr, A), subst1(X, Expr, B)};
subst1(X, Expr, {neg, A}) ->
    {neg, subst1(X, Expr, A)};
subst1(_, _, Q) -> Q.


format_pred({typed, _, E, _}) ->
    format_pred(E);
format_pred({app, _, {'==', _}, [A, B]}) ->
    {eq, format_pred(A), format_pred(B)};
format_pred({app, _, {'!=', _}, [A, B]}) ->
    {neg, {eq, format_pred(A), format_pred(B)}};
format_pred({app, _, {'<', _}, [A, B]}) ->
    {lt, format_pred(A), format_pred(B)};
format_pred({app, _, {'>', _}, [A, B]}) ->
    {lt, format_pred(B), format_pred(A)};
format_pred({app, _, {'=<', _}, [A, B]}) ->
    {neg, {lt, format_pred(B), format_pred(A)}};
format_pred({app, _, {'>=', _}, [A, B]}) ->
    {neg, {lt, format_pred(A), format_pred(B)}};
format_pred(E = {id, _, _}) ->
    E;
format_pred(E = {int, _, _}) ->
    E;
format_pred(E) ->
    error({invalid_qual, E}). %% TODO proper error

simplify([]) ->
    [];
simplify([H|T]) ->
    simplify1(H) ++ simplify(T).

simplify1({Env, {well_formed, T}}) ->
    case T of
        {refined_t, _, _, _} ->
            [{Env, {well_formed, T}}];
        {dep_fun_t, _, _, Args, Ret} ->
            Split =
                fun R(Env0, []) ->
                        [{Env0, {well_formed, Ret}}];
                    R(Env0, [{{id, _, Name}, Type}|Rest]) ->
                        Env1 = bind_var(Name, Type, Env0),
                        [{Env0, {well_formed, Type}}|R(Env1, Rest)]
                end,
            Split(Env, Args)
    end.
