%%%-------------------------------------------------------------------
%%% @author Radosław Rowicki
%%% @doc
%%%     Liquid type checker for Sophia. Refines regular Sophia types
%%%     with dependent constraints and validates them.
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_ast_refine_types).

-export([refine_types/1]).

-type lval() :: integer()
              | aeso_syntax:var()
              | {nu, reference()}
              %% | {length, aeso_syntax:var()}
              .

-type qual() :: {eq, lval(), lval()}
              | {leq, lval(), lval()}
              | {lt, lval(), lval()}
              .

-type ltvar() :: {ltvar, reference()}.

-type predicate() :: [qual()].

-type schema(T) :: {forall, [string()], T}.

-type subst() :: [{string(), qual()}].

-type template() :: schema(predicate() | {subst(), ltvar()}).

fresh_ltvar() ->
    {ltvar, make_ref()}.

fresh_template() ->
    fresh_template([]).
fresh_template(Vars) ->
    {forall, Vars, {[], fresh_ltvar}}.

refine_types(AST) ->
    AST1 = decorate_base_types(AST),
    Cs = generate_constraints(AST1),
    solve_constraints(Cs).

%% Decorates base types with templates through the AST
decorate_base_types(Type = {id, Ann, "int"}) ->
    {liquid, Ann, make_ref(), Type, fresh_template()};
decorate_base_types({typed, Ann, {int, AnnI, I}, {id, AnnT, "int"}}) ->
    Ref = make_ref(),
    {typed, Ann, {int, AnnI, I}, {liquid, AnnT, Ref, {id, AnnT, "int"}, {eq, Ref, I}}};
decorate_base_types(Type = {liquid, _, _, _, _}) ->
    Type;
decorate_base_types([]) -> [];
decorate_base_types([H|T]) -> [decorate_base_types(H)|decorate_base_types(T)];
decorate_base_types(T) when is_tuple(T) ->
    list_to_tuple(decorate_base_types(tuple_to_list(T)));
decorate_base_types(X) -> X.

generate_constraints(AST) ->
    error(todo).

solve_constraints(Cs) ->
    error(todo).
