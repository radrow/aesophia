-module(aeso_ast_refine_types).
-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").
-define(DBG_TEXT_COLOR, "\e[1;33m").
-define(DBG_EXPR_COLOR, "\e[0;1m\e[1m").
-define(DBG_STR_COLOR, "\e[1;32m").
-define(DBG_RESET_COLOR, "\e[0m").
-define(DBG_COLOR(S),
        lists:flatten(
          ?DBG_TEXT_COLOR
          ++ string:replace(
               lists:flatten(
                 string:replace(S, "~s", ?DBG_STR_COLOR ++ "~s" ++ ?DBG_TEXT_COLOR, all)
                ),
               "~p", ?DBG_EXPR_COLOR ++ "~p" ++ ?DBG_TEXT_COLOR, all)
          ++ ?DBG_RESET_COLOR
         )).
-define(DBG(A, B), ?debugFmt(?DBG_COLOR(A), B)).
-define(DBG(A), ?debugMsg(?DBG_COLOR(A))).

-define(refined(Id, T, Q), {refined_t, element(2, T), Id, T, Q}).
-define(refined(T, Q),
        (fun() ->
                 Id = fresh_id(
                        case T of
                            ?int_tp -> "n";
                            ?bool_tp -> "b";
                            ?string_tp -> "s";
                            {id, _, N} -> N;
                            _ -> "v"
                        end
                       ),
                 ?refined(Id, T, apply_subst(nu(), Id, Q))
         end %% Fuck Erlang scoping
        )()).
-define(refined(T), ?refined(T, [])).
-define(op(A, Op, B), {app, [{format, infix}|ann()], {Op, ann()}, [A, B]}).
-define(op(Op, B), {app, [{format, prefix}|ann()], {Op, ann()}, [B]}).

-define(int(I), {int, ann(), I}).
-define(int_tp, {id, _, "int"}).
-define(int_t, {id, ann(), "int"}).

-define(d_pos_int, ?refined(?int_t, [?op(nu(), '>', ?int(0))])).
-define(d_nonneg_int, ?refined(?int_t, [?op(nu(), '>=', ?int(0))])).
%% -define(d_nonzero_int, ?refined(?int_t, [?op(nu(), '!=', ?int(0))])).

-define(bool(B), {bool, ann(), B}).
-define(bool_tp, {id, _, "bool"}).
-define(bool_t, {id, ann(), "bool"}).

%% -define(tuple(S), {tuple, _, S}).
-define(tuple_tp(T), {tuple_t, _, T}).
%% -define(tuple_t(T), {tuple_t, ann(), T}).

-define(tuple_proj_id(N, I),
        {id, ann(), lists:flatten(io_lib:format("$tuple~p.~p", [N, I]))}).
-define(adt_proj_id(QCon, I),
        {id, ann(), lists:flatten(io_lib:format("~s.~p", [string:join(qname(QCon), "."), I]))}).

%% -define(string(S), {string, _, S}).
-define(string_tp, {id, _, "string"}).
%% -define(string_t, {id, ann(), "string"}).

-define(typed(Expr, Type), {typed, element(2, Expr), Expr, Type}).
-define(typed_p(Expr), {typed, _, Expr, _}).
-define(typed_p(Expr, Type), {typed, _, Expr, Type}).


%% -- Types --------------------------------------------------------------------

%% Type imports
-type predicate()   :: aeso_syntax:predicate().
-type expr()        :: aeso_syntax:expr().
-type pat()         :: aeso_syntax:pat().
-type decl()        :: aeso_syntax:decl().
-type letfun()      :: aeso_syntax:letfun().
-type fundecl()     :: aeso_syntax:fundecl().
-type ast()         :: aeso_syntax:ast().
-type type()        :: aeso_syntax:type().
-type dep_type(Q)   :: aeso_syntax:dep_type(Q).
-type dep_arg_t(Q)  :: aeso_syntax:dep_arg_t(Q).
-type id()          :: aeso_syntax:id().
-type qid()         :: aeso_syntax:qid().
-type con()         :: aeso_syntax:con().
-type qcon()        :: aeso_syntax:qcon().
-type ann()         :: aeso_syntax:ann().

-type type_id() :: id() | qid() | con() | qcon().

-type typedef() :: {[aeso_syntax:tvar()], aeso_syntax:typedef()
                   | {contract_t, [aeso_syntax:field_t()]}}.


%% Names
-type name() :: string().
-type qname() :: [name()].

%% Liquid type variable
-type ltvar() :: {ltvar, name()}.

%% Substitution of a variable with an expression
-type subst() :: {name(), expr()}.

%% Uninstantiated predicate template
-type template() :: {template, [subst()], ltvar()}.

-type liquid_qual() ::  predicate() | template().

%% Liquid type, possibly uninstantiated
-type lutype() :: dep_type(liquid_qual()).

-type fun_env() :: #{name() => template()}.
-type var_env() :: #{name() => template()}.
-type type_env() :: [{name(), typedef()}]. % order matters

-record(scope, { fun_env = #{} :: fun_env()
               , type_env = [] :: type_env()
               }).
-type scope() :: #scope{}.

-record(env,
        { scopes           = #{[] => #scope{}} :: #{qname() => scope()}
        , var_env          = #{}               :: var_env()
        , path_pred        = []                :: predicate()
        , cool_ints        = []                :: [integer()]
        , namespace        = []                :: qname()
        }).
-type env() :: #env{}.

%% Grouped subtype constraint
-type subtype_group() :: {subtype_group, [{subtypes, env(), ann(), id(), subst(), liquid_qual()}], type(), ltvar()}.

%% Constraint
-type constr() :: {subtype, ann(), env(), lutype(), lutype()}
                | subtype_group()
                | {well_formed, env(), lutype()}
                | {reachable, ann(), env()}
                | {unreachable, ann(), env()}.

%% Information about ltvar
-record(ltinfo, {id :: id(), base :: type(), predicate :: predicate(), env :: env()}).
-type ltinfo() :: #ltinfo{}.

%% Predicate assignment
-type assignment() :: #{name() => ltinfo()}.

%% Position in type
-type variance() :: contravariant | covariant | forced_covariant | forced_contravariant.

-spec ann() -> ann().
ann() -> [{origin, hagia}].
-spec ann(ann()) -> ann().
ann(L) -> [{origin, hagia}|L].

nu() -> {id, ann(), "$self"}.
-define(nu_p, {id, _, "$self"}).

length() -> {id, ann(), "length"}.

%% -- Name manipulation --------------------------------------------------------

-spec name(aeso_syntax:id() | aeso_syntax:con()) -> name().
name({_, _, X}) -> X.

-spec qname(type_id()) -> qname().
qname({id,   _, X})  -> [X];
qname({qid,  _, Xs}) -> Xs;
qname({con,  _, X})  -> [X];
qname({qcon, _, Xs}) -> Xs.

qid(X) when is_list(X) ->
    qid(ann(), X).
-spec qid(ann(), qname()) -> aeso_syntax:id() | aeso_syntax:qid().
qid(Ann, [X]) -> {id, Ann, X};
qid(Ann, Xs) when is_list(Xs) -> {qid, Ann, Xs}.

id(X) ->
    id(ann(), X).
id(Ann, X) ->
    {id, Ann, X}.

qcon(X) when is_list(X) ->
    qcon(ann(), X).
-spec qcon(ann(), qname()) -> aeso_syntax:con() | aeso_syntax:qcon().
qcon(Ann, [X]) -> {con, Ann, X};
qcon(Ann, Xs)  -> {qcon, Ann, Xs}.

-spec set_qname(qname(), type_id()) -> type_id().
set_qname(Xs, {id,   Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {qid,  Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {con,  Ann, _}) -> qcon(Ann, Xs);
set_qname(Xs, {qcon, Ann, _}) -> qcon(Ann, Xs).


%% -- Environment ---------------------------------------------------------------------

-spec push_scope(aeso_syntax:con(), env()) -> env().
push_scope(Con, Env) ->
    Name   = name(Con),
    New    = Env#env.namespace ++ [Name],
    Scopes = Env#env.scopes,
    Env#env{ namespace = New,
             scopes =
                 case maps:get(New, Scopes, undefined) of
                     undefined -> Scopes#{ New => #scope{} };
                     _         -> Scopes
                 end
           }.

-spec pop_scope(env()) -> env().
pop_scope(Env) ->
    Env#env{ namespace = lists:droplast(Env#env.namespace) }.


-spec get_scope(env(), qname()) -> false | scope().
get_scope(#env{ scopes = Scopes }, Name) ->
    maps:get(Name, Scopes, false).

-spec on_current_scope(env(), fun((scope()) -> scope())) -> env().
on_current_scope(Env = #env{ namespace = NS, scopes = Scopes }, Fun) ->
    Scope = maps:get(NS, Scopes),
    Env#env{ scopes = Scopes#{ NS => Fun(Scope) } }.

-spec on_scopes(env(), fun((scope()) -> scope())) -> env().
on_scopes(Env = #env{ scopes = Scopes }, Fun) ->
    Env#env{ scopes = maps:map(fun(_, Scope) -> Fun(Scope) end, Scopes) }.

-spec bind_var(id(), lutype(), env()) -> env().
bind_var(Id, T, Env = #env{var_env = VarEnv}) ->
    case maps:get(name(Id), VarEnv, none) of
        none -> ok;
        V    ->
            ?DBG("SHADOW OF\n~p\n : ~p IN\n~p", [Id, V, VarEnv]),
            error({jebudu, Id}),
            throw({overwrite, Id})
    end,
    Env#env{ var_env = VarEnv#{name(Id) => T}}.

-spec ensure_var(id(), lutype(), env()) -> env().
ensure_var(Id, T, Env = #env{var_env = VarEnv}) ->
    case maps:get(name(Id), VarEnv, none) of
        none -> Env#env{ var_env = VarEnv#{name(Id) => T}};
        _    -> Env
    end.

-spec bind_nu(lutype(), env()) -> env().
bind_nu(Type, Env) ->
    bind_var(nu(), Type, Env).

-spec bind_vars([{id(), lutype()}], env()) -> env().
bind_vars([], Env) -> Env;
bind_vars([{X, T} | Vars], Env) ->
    bind_vars(Vars, bind_var(X, T, Env)).

-spec bind_args([dep_arg_t(liquid_qual())], env()) -> env().
bind_args([], Env) -> Env;
bind_args([{dep_arg_t, _, X, T} | Vars], Env) ->
    bind_args(Vars, bind_var(X, T, Env)).

-spec bind_fun(name(), lutype(), env()) -> env().
bind_fun(X, Type, Env) ->
    on_current_scope(
      Env, fun(Scope = #scope{ fun_env = Funs }) ->
                   case maps:get(X, Funs, none) of
                       none -> ok;
                       T -> error({jebebebe, X, T, Type})
                   end,
                   Scope#scope{ fun_env = Funs#{X => Type} }
           end).

-spec bind_funs([{name(), lutype()}], env()) -> env().
bind_funs([], Env) -> Env;
bind_funs([{Id, Type} | Rest], Env) ->
    bind_funs(Rest, bind_fun(Id, Type, Env)).

-spec bind_type(id(), [type()], typedef(), env()) -> env().
bind_type(Id, Args, Def, Env) ->
    on_current_scope(Env, fun(Scope = #scope{ type_env = Types }) ->
                                  Scope#scope{ type_env = [{Id, {Args, Def}}|Types] }
                          end).

-spec assert(expr() | predicate(), env()) -> env().
assert(L, Env = #env{path_pred = GP}) when is_list(L) ->
    Env#env{path_pred = L ++ GP};
assert(E, Env = #env{path_pred = GP}) ->
    Env#env{path_pred = [E|GP]}.


%% What scopes could a given name come from?
-spec possible_scopes(env(), qname()) -> [qname()].
possible_scopes(#env{ namespace = Current}, Name) ->
    Qual = lists:droplast(Name),
    [ lists:sublist(Current, I) ++ Qual || I <- lists:seq(0, length(Current)) ].

-spec lookup_type(env(), type_id()) -> false | {qname(), typedef()}.
lookup_type(Env, Id) ->
    lookup_env(Env, type, qname(Id)).

-spec lookup_env(env(), term, qname()) -> false | {qname(), lutype()};
                (env(), type, qname()) -> false | {qname(), typedef()}.
lookup_env(Env, Kind, Name) ->
    Var = case Name of
            [X] when Kind == term -> maps:get(X, Env#env.var_env, false);
            _                     -> false
          end,
    case Var of
        false ->
            Names = [ Qual ++ [lists:last(Name)] || Qual <- possible_scopes(Env, Name) ],
            case [ Res || QName <- Names, Res <- [lookup_env1(Env, Kind, QName)], Res /= false] of
                []    -> false;
                [Res] -> Res;
                Many  ->
                    error({ambiguous_name, [Q || {Q, _} <- Many]})
            end;
        Type -> {Name, Type}
    end.

-spec lookup_env1(env(), term | type, qname()) -> false | {qname(), lutype()}.
lookup_env1(#env{ scopes = Scopes }, Kind, QName) ->
    Qual = lists:droplast(QName),
    Name = lists:last(QName),
    case maps:get(Qual, Scopes, false) of
        false -> false;
        #scope{ fun_env = Funs, type_env = Types } ->
            case case Kind of
                     term -> maps:get(Name, Funs, false);
                     type -> proplists:get_value(Name, Types, false)
                 end of
                false -> false;
                E -> {QName, E}
            end
    end.

-spec type_of(env(), type_id()) -> {qname(), lutype()}.
type_of(Env, Id) ->
    case lookup_env(Env, term, qname(Id)) of
        false ->
            ?DBG("NOT TYPE FOR ~p", [Id]),
            undefined;
        {QId, Ty} -> {set_qname(QId, Id), Ty}
    end.

-spec global_type_binds(env()) -> [{expr(), lutype()}].
global_type_binds(#env{scopes = Scopes}) ->
    [ {qid(ScopePath ++ [Var]), Type}
      || {ScopePath, #scope{fun_env = FEnv}} <- maps:to_list(Scopes),
         {Var, Type} <- maps:to_list(FEnv)
    ].

-spec local_type_binds(env()) -> [{expr(), lutype()}].
local_type_binds(#env{var_env = VEnv}) ->
    [ begin
          Qid = qid(aeso_syntax:get_ann(Type), [Var]),
          {Qid,
           case Type of
               {refined_t, _, Id, _, _} ->
                   apply_subst(Id, Qid, Type);
               {dep_variant_t, _, _, _, _} ->
                   apply_subst(nu(), Qid, Type);
               {dep_list_t, _, _, _} ->
                   apply_subst(length(), Qid, Type);
               _ -> Type
           end
          }
      end
      || {Var, Type} <- maps:to_list(VEnv)
    ].

-spec type_binds(env()) -> [{expr(), lutype()}].
type_binds(Env) ->
    global_type_binds(Env) ++ local_type_binds(Env).


-spec type_defs(env()) -> [{qid(), typedef()}]. %% FIXME really typedef? what about args?
type_defs(#env{scopes = Scopes}) ->
    Types = [ {qid(ScopePath ++ [Var]), TypeDef}
              || {ScopePath, #scope{type_env = TEnv}} <- maps:to_list(Scopes),
                 {Var, TypeDef} <- TEnv
            ],
    lists:reverse(Types).

-spec path_pred(env()) -> predicate().
path_pred(#env{path_pred = PathPred}) ->
    PathPred.


%% -- Initialization -----------------------------------------------------------

-spec init_refiner() -> ok.
init_refiner() ->
    put(ltvar_supply, 0),
    put(id_supply, 0),
    ok.

init_env() ->
    Ann     = ann(),
    Bool    = ?bool_t,
    String  = {id, Ann, "string"},
    Address = {id, Ann, "address"},
    Hash    = {id, Ann, "hash"},
    Bits    = {id, Ann, "bits"},
    Bytes   = fun(Len) -> {bytes_t, Ann, Len} end,
    Unit    = {tuple_t, Ann, []},
    Option  = fun(T) -> {app_t, Ann, {id, Ann, "option"}, [T]} end,
    DFun    = fun(Ts, T) -> {dep_fun_t, Ann, Ts, T} end,
    DFun1   = fun(S, T) -> DFun([S], T) end,
    %% Lambda    = fun(Ts, T) -> {fun_t, Ann, [], Ts, T} end,
    %% Lambda1   = fun(S, T) -> Lambda([S], T) end,
    StateDFun  = fun(Ts, T) -> {dep_fun_t, [stateful|Ann], Ts, T} end,
    Arg     = fun(Name, Type) -> {dep_arg_t, ann(), id(Name), Type} end,

    MkDefs = fun maps:from_list/1,

    ChainScope = #scope
        { fun_env = MkDefs(
                     %% Spend transaction.
                    [{"spend",        StateDFun([Arg("addr", Address), Arg("amount", ?d_nonneg_int)], Unit)},
                     %% Chain environment
                     {"balance",      DFun1(Arg("addr", Address), ?d_nonneg_int)},
                     {"block_hash",   DFun1(Arg("h", ?d_nonneg_int), Option(Hash))},
                     {"timestamp",    ?d_pos_int},
                     {"block_height", ?d_pos_int},
                     {"difficulty",   ?d_nonneg_int},
                     {"gas_limit",    ?d_pos_int}])
        },

    ContractScope = #scope
        { fun_env = MkDefs(
                    [{"balance", ?d_nonneg_int}]) },

    CallScope = #scope
        { fun_env = MkDefs(
                    [{"value",     ?d_nonneg_int},
                     {"gas_price", ?d_pos_int},
                     {"gas_left",  DFun([], ?d_pos_int)}])
        },

    %% Strings
    StringScope = #scope
        { fun_env = MkDefs(
                     [{"length",  DFun1(Arg("str", String), ?d_nonneg_int)}])
        },

    %% Bits
    BitsScope = #scope
        { fun_env = MkDefs(
                     [{"set",     DFun([Arg("bits", Bits), Arg("idx", ?d_nonneg_int)], Bits)},
                      {"clear",   DFun([Arg("bits", Bits), Arg("idx", ?d_nonneg_int)], Bits)},
                      {"test",    DFun([Arg("bits", Bits), Arg("idx", ?d_nonneg_int)], Bool)},
                      {"sum",     DFun1(Arg("bits", Bits), ?d_nonneg_int)}])
                     },

    %% Bytes
    BytesScope = #scope
        { fun_env = MkDefs(
                   [{"to_int", DFun1(Arg("bytes", Bytes(any)), ?d_nonneg_int)}]) },

    TopScope = #scope
        { fun_env  = MkDefs([])
        , type_env =
              [ {"option", {[{tvar, ann(), "'a"}],
                            {variant_t,
                             [ {constr_t, ann(), {con, ann(), "None"}, []}
                             , {constr_t, ann(), {con, ann(), "Some"}, [{tvar, ann(), "'a"}]}
                             ]
                            }
                           }
                }
              ]
        },

    #env{ scopes =
            #{ []           => TopScope
             , ["Chain"]    => ChainScope
             , ["Contract"] => ContractScope
             , ["Call"]     => CallScope
             , ["String"]   => StringScope
             , ["Bits"]     => BitsScope
             , ["Bytes"]    => BytesScope
             } }.

find_cool_ints(Expr) ->
    sets:to_list(find_cool_ints(Expr, sets:from_list([0, 1, -1]))).
find_cool_ints({int, _, I}, Acc) ->
    sets:add_element(-I, sets:add_element(I, Acc));
find_cool_ints({list, _, L}, Acc) ->
    find_cool_ints(L, sets:add_element(length(L), Acc));
find_cool_ints({app, _, {'::', _}, [H, T]}, Acc0) ->
    Acc1 = find_cool_ints([H, T], Acc0),
    sets:union(Acc1,
               sets:from_list([I + 1 || I <- sets:to_list(Acc1)])
              );
find_cool_ints({app, _, {'-', _}, [L, R]}, Acc0) ->
    Acc1 = find_cool_ints([L, R], Acc0),
    AccL = sets:to_list(Acc1),
    sets:union(Acc1,
               sets:from_list([I1 - I2
                               || I1 <- AccL,
                                  I2 <- AccL
                              ])
              );
find_cool_ints({app, _, {'+', _}, [L, R]}, Acc0) ->
    Acc1 = find_cool_ints([L, R], Acc0),
    AccL = sets:to_list(Acc1),
    sets:union(Acc1,
               sets:from_list([I1 + I2
                               || I1 <- AccL,
                                  I2 <- AccL
                              ])
              );
find_cool_ints({app, _, {'++', _}, [L, R]}, Acc0) ->
    Acc1 = find_cool_ints([L, R], Acc0),
    AccL = sets:to_list(Acc1),
    sets:union(Acc1,
               sets:from_list([I1 + I2
                               || I1 <- AccL,
                                  I2 <- AccL
                              ])
              );
find_cool_ints([H|T], Acc) ->
    find_cool_ints(T, find_cool_ints(H, Acc));
find_cool_ints(T, Acc) when is_tuple(T) ->
    find_cool_ints(tuple_to_list(T), Acc);
find_cool_ints(M, Acc) when is_map(M) ->
    find_cool_ints(maps:to_list(M), Acc);
find_cool_ints(_, Acc) ->
    Acc.

with_cool_ints_from(AST, Env = #env{cool_ints = CI}) ->
    Env#env{cool_ints = find_cool_ints(AST) ++ CI}.


find_tuple_sizes(Expr) ->
    sets:to_list(find_tuple_sizes(Expr, sets:new())).
find_tuple_sizes({tuple_t, _, T}, Acc) ->
    find_tuple_sizes(T, sets:add_element(length(T), Acc));
find_tuple_sizes({tuple, _, T}, Acc) ->
    find_tuple_sizes(T, sets:add_element(length(T), Acc));
find_tuple_sizes([H|T], Acc) ->
    find_tuple_sizes(T, find_tuple_sizes(H, Acc));
find_tuple_sizes(T, Acc) when is_tuple(T) ->
    find_tuple_sizes(tuple_to_list(T), Acc);
find_tuple_sizes(_, Acc) ->
    Acc.

-spec bind_ast_funs(aeso_ast_infer_types:env(), ast(), env()) -> env().
bind_ast_funs(TCEnv, AST, Env) ->
    lists:foldr(
      fun({HEAD, _, Con, Defs}, Env0)
            when HEAD =:= namespace;
                 HEAD =:= contract;
                 HEAD =:= contract_main;
                 HEAD =:= contract_interface ->
              Env1 = push_scope(Con, Env0),
              Env2 = bind_funs(
                       [ begin
                             {_, {_, {type_sig, TSAnn, _, [], ArgsT, RetT}}} =
                                 aeso_ast_infer_types:lookup_env(
                                   TCEnv, term, FAnn, qname(Con) ++ qname(Id)),
                             check_arg_assumptions(Id, FAnn, ArgsT),
                             DepArgsT =
                                 [ fresh_liquid_arg(Env, Arg, ArgT)
                                   || {?typed_p(Arg), ArgT} <- lists:zip(Args, ArgsT)
                                 ],
                             RetT1 =
                                 apply_subst(
                                   [ {PreId, Arg}
                                     || {?typed_p(Arg), {refined_t, _, PreId, _, _}}
                                           <- lists:zip(Args, ArgsT)
                                   ],
                                   RetT
                                  ),
                             DepRetT = fresh_liquid(Env1, "rete", RetT1),
                             ?DBG("RETT ~p", [DepRetT]),
                             TypeDep = {dep_fun_t, TSAnn, DepArgsT, DepRetT},
                             {Name, TypeDep}
                         end
                         || {letfun, FAnn, Id = {id, _, Name}, Args, _, _} <- Defs
                       ],
                       Env1),
              Env3 = bind_funs(
                       [ {Name, fresh_liquid(Env2, Name, Type)}
                         || {fun_decl, _, {id, _, Name}, Type} <- Defs
                       ],
                       Env2),
              Env4 = pop_scope(Env3),
              Env4
      end,
     Env, AST).

check_arg_assumptions({id, _, Name}, Ann, Args) ->
    case proplists:get_value(entrypoint, Ann, false) of
        true ->
            [ case has_assumptions(Arg) of
                  true -> throw({entrypoint_arg_assump, {Name, Ann, Arg}});
                  false -> ok
              end
              || Arg <- Args
            ];
        false -> ok
    end.

%% Check if the type is not strictly less general than its base type
has_assumptions(T) ->
    has_assumptions(covariant, T).
has_assumptions(covariant, {refined_t, _, _, _, [_|_]}) ->
    true;
has_assumptions(covariant, {dep_variant_t, _, _, [_|_], _}) ->
    true;
has_assumptions(covariant, {dep_list_t, _, _, [_|_]}) ->
    true;
has_assumptions(Variance, {dep_fun_t, _, Args, RetT}) ->
    has_assumptions(switch_variance(Variance), Args)
        orelse has_assumptions(Variance, RetT);
has_assumptions(Variance, {fun_t, _, Named, Args, RetT}) ->
    has_assumptions(switch_variance(Variance), Args)
        orelse has_assumptions(switch_variance(Variance), Named)
        orelse has_assumptions(Variance, RetT);
has_assumptions(Variance, {type_sig, _, _, Named, Args, RetT}) ->
    has_assumptions(switch_variance(Variance), Args)
        orelse has_assumptions(switch_variance(Variance), Named)
        orelse has_assumptions(Variance, RetT);
has_assumptions(Variance, {app_t, _, {id, _, "map"}, [K, V]}) ->
    has_assumptions(switch_variance(Variance), K)
        orelse has_assumptions(Variance, V);
has_assumptions(Variance, {tuple_t, _, Args}) ->
    has_assumptions(Variance, Args);
has_assumptions(Variance, {dep_record_t, _, _, Fields}) ->
    has_assumptions(Variance, Fields);
has_assumptions(Variance, {dep_variant_t, _, _, _, Constrs}) ->
    has_assumptions(Variance, Constrs);
has_assumptions(Variance, {dep_list_t, _, ElemT, _}) ->
    has_assumptions(Variance, ElemT);
has_assumptions(Variance, [H|T]) ->
    has_assumptions(Variance, H) orelse has_assumptions(Variance, T);
has_assumptions(Variance, T) when is_tuple(T) ->
    has_assumptions(Variance, tuple_to_list(T));
has_assumptions(_, _) ->
    false.

%% -- Fresh stuff --------------------------------------------------------------

-spec fresh_ltvar(name()) -> ltvar().
fresh_ltvar(Name) ->
    I = get(ltvar_supply),
    put(ltvar_supply, I + 1),
    {ltvar, Name ++ "_" ++ integer_to_list(I)}.

-spec fresh_template(name()) -> lutype().
fresh_template(Name) -> fresh_template(covariant, Name).
fresh_template(covariant, Name) -> {template, [], fresh_ltvar(Name)};
fresh_template(contravariant, _) -> [];
fresh_template(forced_covariant, Name) -> fresh_template(covariant, Name);
fresh_template(forced_contravariant, Name) -> fresh_template(contravariant, Name).

-spec fresh_name(name()) -> name().
fresh_name(Name) ->
    I = get(id_supply),
    put(id_supply, I + 1),
    Name ++ "_" ++ integer_to_list(I).

-spec fresh_id(name()) -> type_id().
fresh_id(Name) ->
    N = fresh_name(Name),
    {id, ann(), N}.
fresh_id(Name, Type) ->
    Id = fresh_id(Name),
    ?typed(Id, Type).

fresh_nu() -> fresh_id("self").

%% Decorates base types with templates through the AST
-spec fresh_liquid(env(), name(), term()) -> term().
fresh_liquid(Env, Hint, Type) ->
    fresh_liquid(Env, covariant, Hint, Type).

-spec fresh_liquid(env(), name(), variance(), term()) -> term().
fresh_liquid(_Env, _Variance, _Hint, Type = {refined_t, _, _, _, _}) ->
    Type;
fresh_liquid(_Env, _Variance, _Hint, Type = {dep_fun_t, _, _, _}) ->
    Type;
fresh_liquid(_Env, _Variance, _Hint, Type = {dep_arg_t, _, _, _}) ->
    Type;
fresh_liquid(Env, Variance, _, {dep_record_t, Ann, Rec, Fields}) ->
    Qid = case Rec of
              {app_t, _, Q, _} -> Q;
              _ -> Rec
          end,
    {dep_record_t, Ann, Rec,
     [ fresh_liquid_field(Env, Variance, Qid, Field, FType)
       || {field_t, _, Field, FType} <- Fields
     ]
    };
fresh_liquid(Env, Variance, Hint, {dep_variant_t, Ann, Type, TagPred, Constrs}) ->
    {dep_variant_t, Ann, Type, TagPred,
     [ {dep_constr_t, CAnn, Con,
        fresh_liquid(Env, Variance, Hint ++ "_" ++ name(Con), Vals)}
       || {constr_t, CAnn, Con, Vals} <- Constrs
     ]
    };
%% fresh_liquid(_Env, _Variance, _Hint, Type = {dep_constr_t, _, _, _}) ->
%%     Type;
fresh_liquid(Env, Variance, Hint, {dep_list_t, Ann, ElemT, LenPred}) ->
    {dep_list_t, Ann, fresh_liquid(Env, Variance, Hint, ElemT), LenPred};
fresh_liquid(_Env, Variance, Hint, Type = {id, Ann, Name}) ->
    {refined_t, Ann,
     fresh_id(case Name of
                  "int" -> "n";
                  "bool" -> "p";
                  "string" -> "s";
                  _ -> Name
              end),
     Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {con, Ann, Name}) ->
    {refined_t, Ann, fresh_id(string:to_lower(Name)), Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {qcon, Ann, Name}) ->
    {refined_t, Ann, fresh_id(string:to_lower(lists:last(Name))), Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {tvar, Ann, [_|Name]}) ->
    {refined_t, Ann, fresh_id(Name), Type, fresh_template(Variance, Hint)};
fresh_liquid(Env, Variance, Hint, Type = {qid, Ann, _}) ->
    fresh_liquid(Env, Variance, Hint, {app_t, Ann, Type, []});
fresh_liquid(Env, Variance, Hint, {app_t, Ann, Id = {id, _, "map"}, [K, V]}) ->
    {app_t, Ann, Id,
     [ fresh_liquid(Env, switch_variance(Variance), Hint ++ "_key", K)
     , fresh_liquid(Env,                  Variance, Hint ++ "_val", V)
     ]};
fresh_liquid(Env, Variance, Hint, {app_t, Ann, {id, _, "list"}, [Elem]})
  when Variance =:= contravariant; Variance =:= forced_contravariant ->
    {dep_list_t, Ann, fresh_liquid(Env, Variance, Hint, Elem), [?op(length(), '>=', ?int(0))]};
fresh_liquid(Env, Variance, Hint, {app_t, Ann, {id, _, "list"}, [Elem]}) ->
    {dep_list_t, Ann, fresh_liquid(Env, Variance, Hint, Elem),
     fresh_template(Variance, Hint)};
fresh_liquid(Env, Variance, Hint, {app_t, Ann, {id, IAnn, Name}, Args}) ->
    fresh_liquid(Env, Variance, Hint, {app_t, Ann, {qid, IAnn, [Name]}, Args});
fresh_liquid(Env, Variance, Hint,
             Type = {app_t, _, Qid = {qid, Ann, _}, Args}) ->
    case lookup_type(Env, Qid) of
        false ->
            error({undefined_type, Qid});
        {_, {TArgs, TDef}} ->
            Subst = lists:zip(TArgs, Args),
            case TDef of
                {alias_t, Type1} ->
                    fresh_liquid(Env, Variance, Hint, apply_subst(Subst, Type1));
                {record_t, Fields} ->
                    {dep_record_t, Ann, Type,
                     [ fresh_liquid_field(Env, Variance, Qid, Field, apply_subst(Subst, FType))
                      || {field_t, _, Field, FType} <- Fields
                     ]
                    };
                {variant_t, Constrs} ->
                    DepConstrs =
                        [ {dep_constr_t, CAnn, Con,
                           fresh_liquid(Env, Variance, Hint ++ "_" ++ name(Con),
                                        apply_subst(Subst, Vals))}
                          || {constr_t, CAnn, Con, Vals} <- Constrs
                        ],
                    {dep_variant_t, Ann, Type,
                     fresh_template(Variance, Hint ++ "_tag"), DepConstrs}
            end
    end;
fresh_liquid(Env, Variance, Hint, {type_sig, Ann, _, Named, Args, Ret}) ->
    fresh_liquid(Env, Variance, Hint, {fun_t, Ann, Named, Args, Ret});
fresh_liquid(Env, Variance, Hint, {fun_t, Ann, Named, Args, Ret}) ->
    { dep_fun_t, Ann
    , [ fresh_liquid_arg(Env, switch_variance(Variance), Id, Type)
       || {named_arg_t, _, Id, Type, _} <- Named
      ]
      ++ [ begin
               ArgT = fresh_liquid(Env, switch_variance(Variance), Hint ++ "_argtt", Arg),
               ArgId = case ArgT of
                           {refined_t, _, Id, _, _} -> Id;
                           _ -> fresh_id("arg")
                       end,
               {dep_arg_t, aeso_syntax:get_ann(Arg), ArgId, ArgT}
           end
          || Arg <- Args]
    , fresh_liquid(Env, Variance, Hint, Ret)
    };
fresh_liquid(Env, Variance, Hint, {tuple_t, Ann, Types}) ->
    {tuple_t, Ann, fresh_liquid(Env, Variance, Hint, Types)};
fresh_liquid(_Env, _, _, []) -> [];
fresh_liquid(Env, Variance, Hint, [H|T]) ->
    [fresh_liquid(Env, Variance, Hint, H)|fresh_liquid(Env, Variance, Hint, T)];
fresh_liquid(Env, Variance, Hint, T) when is_tuple(T) ->
    list_to_tuple(fresh_liquid(Env, Variance, Hint, tuple_to_list(T)));
fresh_liquid(_Env, _, _, X) -> X.

fresh_liquid_arg(Env, Id, Type) ->
    fresh_liquid_arg(Env, contravariant, Id, Type).
fresh_liquid_arg(Env, Variance, Id, Type) ->
    DepType =
        case fresh_liquid(Env, Variance, name(Id), Type) of
            {refined_t, Ann, TId, Base, Pred} ->
                {refined_t, Ann, Id, Base, apply_subst(TId, Id, Pred)};
            T -> T
        end,
    {dep_arg_t, aeso_syntax:get_ann(Id), Id, DepType}.

fresh_liquid_field(Env, Variance, _, Id, Type) ->
    {dep_arg_t, A, I, DT} = fresh_liquid_arg(Env, Variance, Id, Type),
    {dep_field_t, A, I, DT}.

-spec switch_variance(variance()) -> variance().
switch_variance(covariant) ->
    contravariant;
switch_variance(contravariant) ->
    covariant;
switch_variance(forced_covariant) ->
    forced_covariant;
switch_variance(forced_contravariant) ->
    forced_contravariant.


%% -- Entrypoint ---------------------------------------------------------------

refine_ast(TCEnv, AST) ->
    Env0 = init_env(),
    Env1 = with_cool_ints_from(TCEnv, with_cool_ints_from(AST, Env0)),
    ?DBG("COOL INTS: ~p", [Env1#env.cool_ints]),
    Env2 = register_typedefs(AST, Env1),
    try
        Env3 = bind_ast_funs(TCEnv, AST, Env2),
        {AST1, CS0} = constr_ast(Env3, AST),
        CS1 = split_constr(CS0),
        CS2 = group_subtypes(CS1),
        case aeso_smt:scoped(
          fun() ->
                  declare_tuples(find_tuple_sizes(AST)),
                  declare_datatypes(type_defs(Env3)),
                  solve(Env3, CS2)
          end) of
            Assg ->
                AST2 = apply_assg(Assg, AST1),
                {ok, AST2}
        end
    catch {ErrType, _}=E
                when ErrType =:= contradict;
                     ErrType =:= invalid_reachable;
                     ErrType =:= valid_unreachable;
                     ErrType =:= overwrite;
                     ErrType =:= entrypoint_arg_assump
                     -> {error, E}
    end.


%% -- Constraint generation ----------------------------------------------------

-spec constr_ast(env(), ast()) -> {ast(), [constr()]}.
constr_ast(Env, AST) ->
    lists:foldr(
      fun(Def, {Decls, S00}) ->
              {Decl, S01} = constr_con(Env, Def, S00),
              {[Decl|Decls], S01}
      end,
      {[], []}, AST
     ).

-spec constr_con(env(), decl(), [constr()]) -> {decl(), [constr()]}.
constr_con(Env0, {Tag, Ann, Con, Defs}, S0)
  when Tag =:= contract;
       Tag =:= namespace ->
    Env1 = push_scope(Con, Env0),
    {Defs1, S1} =
        lists:foldr(
          fun(Def, {Decls, S00}) when element(1, Def) =:= letfun ->
                  {Decl, S01} = constr_letfun(Env1, Def, S00),
                  {[Decl|Decls], S01};
             (_, Acc) -> Acc
          end,
          {[], S0}, Defs
         ),
    {{Tag, Ann, Con, Defs1}, S1}.

-spec constr_letfun(env(), letfun(), [constr()]) -> {fundecl(), [constr()]}.
constr_letfun(Env0, {letfun, Ann, Id, Args, _, Body}, S0) ->
    ?DBG("BODY ~p", [Body]),
    {_, GlobFunT = {dep_fun_t, _, GlobArgsT, _}} = type_of(Env0, Id),
    ArgsT =
        [ case Arg of
              ?typed_p(Arg1) -> {dep_arg_t, ArgAnn, Arg1, ArgT};
              {dep_arg_t, _, _, _} -> Arg
          end
         || {Arg,
             {dep_arg_t, ArgAnn, _, ArgT}
            } <- lists:zip(Args, GlobArgsT)
        ],
    Env1 = bind_args(ArgsT, Env0),
    Body1 = a_normalize(Body),
    ?DBG("NORMALIZED\n~s\nTO\n~s", [aeso_pretty:pp(expr, Body), aeso_pretty:pp(expr, Body1)]),
    {BodyT, S1} = constr_expr(Env1, Body1, S0),
    InnerFunT = {dep_fun_t, Ann, ArgsT, BodyT},
    ?DBG("\nINNER:\n~p\n\nOUTER:\n~p", [InnerFunT, GlobFunT]),
    S3 = [ {subtype, Ann, Env0, InnerFunT, GlobFunT}
         , {well_formed, Env0, GlobFunT}
         , {well_formed, Env0, InnerFunT}
         | S1
         ],

    {{fun_decl, Ann, Id, GlobFunT}, S3}.

register_typedefs([{Tag, _, Con, Defs}|Rest], Env0)
  when Tag =:= contract;
       Tag =:= namespace ->
    Env1 = push_scope(Con, Env0),
    Env2 = register_typedefs(Defs, Env1),
    Env3 = pop_scope(Env2),
    register_typedefs(Rest, Env3);
register_typedefs([{type_def, _, Id, Args, TDef}|Rest], Env) ->
    register_typedefs(Rest, bind_type(name(Id), Args, TDef, Env));
register_typedefs([_|Rest], Env) ->
    register_typedefs(Rest, Env);
register_typedefs([], Env) ->
    Env.


constr_expr_list(Env, Es, S) ->
    constr_expr_list(Env, Es, [], S).
constr_expr_list(_, [], Acc, S) ->
    {lists:reverse(Acc), S};
constr_expr_list(Env, [H|T], Acc, S0) ->
    {H1, S1} = constr_expr(Env, H, S0),
    constr_expr_list(Env, T, [H1|Acc], S1).

constr_expr(Env, ?typed_p(Expr, Type = {refined_t, Ann, _, Base, _}), S0) ->
    {ExprT, S1} = constr_expr(Env, Expr, Base, S0),
    {ExprT,
     [ {subtype, Ann, Env, ExprT, Type}
     | S1
     ]
    };
constr_expr(Env, ?typed_p(Expr, T), S) ->
    constr_expr(Env, Expr, T, S);
constr_expr(_, X, _) ->
    error({untyped, X}).

constr_expr(Env, {app, Ann, F, Args}, RetT, S)
  when element(1, F) =/= typed ->
    %% Here we fix the untyped operators
    ArgTypes = [ArgT || {typed, _, _, ArgT} <- Args],
    TypedF = {typed, Ann, F, {fun_t, Ann, [], ArgTypes, RetT}},
    constr_expr(Env, {app, Ann, TypedF, Args}, RetT, S);
constr_expr(Env, {block, Ann, Stmts}, T, S) ->
    ExprT = fresh_liquid(Env, "block", T),
    {RestT, S1} = constr_expr(Env, Stmts, T, S),
    { ExprT,
     [ {well_formed, Env, ExprT}
     , {subtype, Ann, Env, RestT, ExprT}
     | S1
     ]
    };
constr_expr(Env, {typed, Ann, E, T1}, T2, S0) ->
    DT2 = fresh_liquid(Env, "t", T2),
    {DT1, S1} = constr_expr(Env, E, T1, S0),
    {DT2,
     [ {well_formed, Env, DT2}
     , {subtype, Ann, Env, DT1, DT2}
     | S1
     ]
    };
constr_expr(Env, Expr = {IdHead, Ann, Name}, T, S)
  when IdHead =:= id; IdHead =:= qid ->
    case element(1, T) =:= id orelse element(1, T) =:= tvar of
        true ->
            {?refined(T, [?op(nu(), '==', Expr)]), S};
        _ -> {_, DT} = type_of(Env, Expr),
             TExpr = fresh_liquid(Env, Name, T),
             {TExpr
             , [ {subtype, Ann, Env, DT, TExpr}
               , {well_formed, Env, TExpr}
               | S
               ]
             }
    end;
constr_expr(_Env, I = {int, _, _}, T = ?int_tp, S) ->
    {?refined(T, [?op(nu(), '==', I)]), S};
constr_expr(_Env, {bool, _, B}, T, S) ->
    {?refined(T, [if B -> nu(); true -> ?op('!', nu()) end]), S};

constr_expr(Env, {tuple, Ann, Elems}, _, S0) ->
    {ElemsT, S1} = constr_expr_list(Env, Elems, S0),
    {{tuple_t, Ann, ElemsT},
     S1
    };

constr_expr(Env, {record, Ann, FieldVals}, T, S0) ->
    {Fields, Vals} =
        lists:unzip([{Field, Val} || {field, _, [{proj, _, Field}], Val} <- FieldVals]),
    {ValsT, S1} = constr_expr_list(Env, Vals, S0),
    {{dep_record_t, Ann, T,
      [{dep_field_t, aeso_syntax:get_ann(Field), Field, ValT}
       || {Field, ValT} <- lists:zip(Fields, ValsT)]},
     S1
    };

constr_expr(_Env, Expr = {CmpOp, Ann}, {fun_t, _, _, [OpLT, OpRT], RetT = ?bool_tp}, S)
  when CmpOp =:= '<';
       CmpOp =:= '=<';
       CmpOp =:= '>';
       CmpOp =:= '>=';
       CmpOp =:= '==';
       CmpOp =:= '!=' ->
    OpLV = fresh_id("opl"),
    OpRV = fresh_id("opr"),
    { {dep_fun_t, Ann,
       [ {dep_arg_t, aeso_syntax:get_ann(OpLT), OpLV, ?refined(OpLV, OpLT, [])}
       , {dep_arg_t, aeso_syntax:get_ann(OpRT), OpRV, ?refined(OpRV, OpRT, [])}
       ],
       ?refined(RetT, [?op(nu(), '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
      }
    , S
    };
constr_expr(_Env, Expr = {CmpOp, Ann}, {fun_t, _, _, [OpLT, OpRT], RetT = ?int_tp}, S)
  when CmpOp =:= '+';
       CmpOp =:= '*';
       CmpOp =:= '-';
       CmpOp =:= '/';
       CmpOp =:= 'mod';
       CmpOp =:= '^' ->
    OpLV = fresh_id("opl"),
    OpRV = fresh_id("opr"),
    { {dep_fun_t, Ann,
       [ {dep_arg_t, aeso_syntax:get_ann(OpLT), OpLV, ?refined(OpLV, OpLT, [])}
       , {dep_arg_t, aeso_syntax:get_ann(OpRT), OpRV,
          ?refined(OpRV, OpRT,
                   case CmpOp of
                       'mod' -> [?op(nu(), '>',  ?int(0))];
                       '/'   -> [?op(nu(), '!=', ?int(0))];
                       '^'   -> [?op(nu(), '>=', ?int(0))];
                       _     -> []
                   end)}
       ], ?refined(RetT, [?op(nu(), '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
      }
    , S
    };
constr_expr(_Env, Expr = {'-', Ann}, _, S) ->
    N = fresh_id("n"),
    { {dep_fun_t, Ann,
       [{dep_arg_t, Ann, N, ?refined(N, ?int_t, [])}],
       ?refined(?int_t,
                [?op(nu(), '==', {app, [{format, prefix}|Ann], Expr, [N]})])
      }
    , S
    };
constr_expr(Env, {app, Ann, ?typed_p({'::', _}), [OpL, OpR]}, {app_t, _, {id, _, "list"}, [ElemT]}, S0) ->
    {DepElemLT, S1} = constr_expr(Env, OpL, S0),
    {{dep_list_t, _, DepElemRT, _}, S2} = constr_expr(Env, OpR, S1),
    DepElemT = fresh_liquid(Env, "elem_cat", ElemT),
    LenPred = [?op(length(), '==', ?op(OpR, '+', ?int(1)))],
    {{dep_list_t, Ann, DepElemT, LenPred},
     [ {well_formed, Env, DepElemT}
     , {subtype, Ann, Env, DepElemLT, DepElemT}
     , {subtype, Ann, Env, DepElemRT, DepElemT}
     | S2
     ]
    };
constr_expr(Env, {app, Ann, ?typed_p({'++', _}), [OpL, OpR]}, {app_t, _, {id, _, "list"}, [ElemT]}, S0) ->
    {{dep_list_t, _, DepElemLT, _}, S1} = constr_expr(Env, OpL, S0),
    {{dep_list_t, _, DepElemRT, _}, S2} = constr_expr(Env, OpR, S1),
    DepElemT = fresh_liquid(Env, "elem_cat", ElemT),
    LenPred = [?op(length(), '==', ?op(OpL, '+', OpR))],
    {{dep_list_t, Ann, DepElemT, LenPred},
     [ {well_formed, Env, DepElemT}
     , {subtype, Ann, Env, DepElemLT, DepElemT}
     , {subtype, Ann, Env, DepElemRT, DepElemT}
     | S2
     ]
    };
constr_expr(Env, {app, Ann, ?typed_p({id, _, "abort"}), _}, T, S0) ->
    ExprT = fresh_liquid(Env, "abort", T),
    {ExprT,
     [ {unreachable, Ann, Env}
     , {well_formed, Env, ExprT}
     |S0
     ]
    };
constr_expr(Env, {con, Ann, "None"}, Type, S0) ->
    constr_expr(Env, {app, Ann, ?typed({qcon, Ann, ["None"]}, Type), []}, Type, S0);
constr_expr(Env, QCon = {qcon, Ann, _}, Type = {fun_t, _, _, ArgsT, RetT}, S0) ->
    %% Lambda-constructor
    Args = [ fresh_id("con_arg", ArgT) || ArgT <- ArgsT],
    Lam =
        {lam, Ann,
         [ {arg, aeso_syntax:get_ann(ArgT), Arg, ArgT}
           || {?typed_p(Arg), ArgT} <- lists:zip(Args, ArgsT)
         ],
         ?typed({app, Ann, QCon, Args}, RetT)
        },
    constr_expr(Env, Lam, Type, S0);
constr_expr(Env, QCon = {qcon, Ann, _}, Type, S0) ->
    %% Nullary constructor
    constr_expr(Env, {app, Ann, ?typed(QCon, Type), []}, Type, S0);
constr_expr(Env, {app, Ann, ?typed_p({con, CAnn, "Some"}, CType), Args}, Type, S0) ->
    constr_expr(Env, {app, Ann, ?typed({qcon, CAnn, ["Some"]}, CType), Args}, Type, S0);
constr_expr(Env, {app, Ann, ?typed_p(QCon = {qcon, _, QName}), Args}, Type, S0) ->
    {TypeQid, AppliedTypeArgs} =
        case Type of
            {qid, _, _} -> {Type, []};
            {app_t, _, T, A} -> {T, A}
        end,
    {ArgsT, S1} = constr_expr_list(Env, Args, S0),
    {_, {DeclaredTypeArgs, {variant_t, Constrs}}} = lookup_type(Env, TypeQid),
    TypeSubst = lists:zip(DeclaredTypeArgs, AppliedTypeArgs),

    DepConstrs =
        [ {dep_constr_t, CAnn, Con,
           case lists:last(QName) == name(Con) of
               true  -> ArgsT;
               false -> [?refined(Arg, [?bool(false)]) || Arg <- ConArgs]
           end
          }
          || {constr_t, CAnn, Con, ConArgs} <- Constrs
        ],
    {{dep_variant_t, Ann, Type, [{is_tag, Ann, nu(), QCon, ArgsT}],
      apply_subst(TypeSubst, DepConstrs)},
     S1
    };
constr_expr(Env, {app, Ann, F = ?typed_p(_, {fun_t, _, NamedT, _, _}), Args0}, _, S0) ->
    NamedArgs = [Arg || Arg = {named_arg, _, _, _} <- Args0],
    Args =
        [ case [ArgValue
                || {named_arg, _, ArgName, ArgValue} <- NamedArgs,
                   ArgName == TArgName
               ] of
              [Arg] -> Arg;
              [] -> TArgDefault
          end
         || {named_arg_t, _, TArgName, _, TArgDefault} <- NamedT
        ] ++ (Args0 -- NamedArgs),
    {{dep_fun_t, _, ArgsFT, RetT}, S1} = constr_expr(Env, F, S0),
    {ArgsT, S2} = constr_expr_list(Env, Args, S1),
    ArgSubst = [{X, Expr} || {{dep_arg_t, _, X, _}, Expr} <- lists:zip(ArgsFT, Args)],
    { apply_subst(ArgSubst, RetT)
    , [{subtype, [{context, {app, Ann, F, N}}|aeso_syntax:get_ann(ArgT)],
        Env, ArgT, ArgFT}
       || {{dep_arg_t, _, _, ArgFT}, ArgT, N} <- lists:zip3(ArgsFT, ArgsT, lists:seq(1, length(ArgsT)))
      ] ++ S2
    };
constr_expr(Env, {'if', _, Cond, Then, Else}, T, S0) ->
    ExprT = fresh_liquid(Env, "if", T),
    {_, S1} = constr_expr(Env, Cond, S0),
    EnvThen = assert(Cond, Env),
    EnvElse = assert(?op('!', Cond), Env),
    {ThenT, S2} = constr_expr(EnvThen, Then, S1),
    {ElseT, S3} = constr_expr(EnvElse,Else, S2),
    { ExprT
    , [ {well_formed, Env, ExprT}
      , {reachable, aeso_syntax:get_ann(Then), EnvThen}
      , {reachable, aeso_syntax:get_ann(Else), EnvElse}
      , {subtype, [{context, then}|aeso_syntax:get_ann(Then)], EnvThen, ThenT, ExprT}
      , {subtype, [{context, else}|aeso_syntax:get_ann(Else)], EnvElse, ElseT, ExprT}
      | S3
      ]
    };
constr_expr(Env, {switch, _, Switched, Alts}, T, S0) ->
    ExprT = fresh_liquid(Env, "switch", T),
    {SwitchedT, S1} = constr_expr(Env, Switched, S0),
    S2 = constr_cases(Env, Switched, SwitchedT, ExprT, Alts, S1),
    {ExprT
    , [{well_formed, Env, ExprT}|S2]
    };
constr_expr(Env, {lam, _, Args, Body}, {fun_t, TAnn, _, _, RetT}, S0) ->
    DepArgsT =
        [ fresh_liquid_arg(Env, ArgId, ArgT)
         || {arg, _, ArgId, ArgT} <- Args
        ],
    DepRetT = fresh_liquid(Env, "lam", RetT),
    ?DBG("LAM RET ~p\n -> ~p", [DepArgsT, DepRetT]),
    ExprT = {dep_fun_t, TAnn, DepArgsT, DepRetT},
    EnvBody = bind_args(DepArgsT, Env),
    {BodyT, S1} = constr_expr(EnvBody, Body, S0),
    {ExprT,
     [ {well_formed, Env, {dep_fun_t, ann(), DepArgsT, DepRetT}}
     , {subtype, aeso_syntax:get_ann(Body), EnvBody, BodyT, DepRetT}
     | S1
     ]
    };
constr_expr(Env, {proj, Ann, Rec, Field}, T, S0) ->
    ExprT = fresh_liquid(Env, "proj", T),
    {{dep_record_t, _, _, Fields}, S1} = constr_expr(Env, Rec, S0),
    [FieldT] =
        [ RecFieldT
         || {dep_field_t, _, RecFieldName, RecFieldT} <- Fields,
            name(Field) == name(RecFieldName)
        ],
    {ExprT,
     [ {well_formed, Env, ExprT}
     , {subtype, Ann, Env, FieldT, ExprT}
     | S1
     ]
    };
constr_expr(Env, {list, Ann, Elems}, {app_t, TAnn, _, [ElemT]}, S0) ->
    DepElemT = fresh_liquid(Env, "list", ElemT),
    {DepElemsT, S1} = constr_expr_list(Env, Elems, S0),
    S2 =
        [ {subtype, Ann, Env, DepElemTI, DepElemT}
         || DepElemTI <- DepElemsT
        ] ++ S1,
    {{dep_list_t, TAnn, DepElemT, [?op(length(), '==', ?int(length(Elems)))]},
     [ {well_formed, Env, DepElemT}
     | S2
     ]
    };

constr_expr(Env, [E], T, S0) ->
    constr_expr(Env, E, T, S0);
constr_expr(Env0, [{letval, Ann, Pat, Val}|Rest], T, S0) ->
    ExprT = fresh_liquid(Env0, "letval", T),
    {ValT, S1} = constr_expr(Env0, Val, S0),
    {Env1, EnvFail} = match_to_pattern(Env0, Pat, Val, ValT),
    {RestT, S2} = constr_expr(Env1, Rest, T, S1),
    {ExprT,
     [ {well_formed, Env0, ExprT}
     , {subtype, Ann, Env1, RestT, ExprT}
     , {unreachable, Ann, EnvFail}
     | S2
     ]
    };
constr_expr(Env0, [{letfun, Ann, Id, Args, RetT, Body}|Rest], T, S0) ->
    ArgsTypes = [ArgT || {typed, _, _, ArgT} <- Args],
    ExprT = {fun_t, Ann, [], ArgsTypes, RetT},
    constr_expr(
      Env0,
      [ {letval, Ann, ?typed(Id, ExprT),
         ?typed(
            {lam, Ann,
             [ {arg, ArgAnn, ArgId, ArgT}
               || {typed, ArgAnn, ArgId, ArgT} <- Args
             ], Body},
            ExprT)
           }
      | Rest
      ], T, S0
     );
constr_expr(Env,
            [ ?typed_p({app, Ann, {typed, _, {id, _, "require"}, _}, [Cond, _]})
            | Rest
            ], T, S0) ->
    Env1 = assert(Cond, Env),
    constr_expr(Env1, Rest, T, [{reachable, Ann, Env1}|S0]);
constr_expr(_Env, {string, _, _}, T, S0) ->
    {?refined(T), S0};
constr_expr(Env, [Expr|Rest], T, S0) ->
    ExprT = fresh_liquid(Env, "expr", T),
    {_, S1} = constr_expr(Env, Expr, S0),
    {RestT, S2} = constr_expr(Env, Rest, T, S1),
    {ExprT,
     [ {well_formed, Env, ExprT}
     , {subtype, aeso_syntax:get_ann(Expr), Env, RestT, ExprT}
     | S2
     ]
    };
constr_expr(_Env, [], T, S) ->
    {T, S};
constr_expr(_, A, B, _) ->
    error({todo, A, B}).

constr_cases(_Env, _Switched, _SwitchedT, _ExprT, Alts, S) ->
    constr_cases(_Env, _Switched, _SwitchedT, _ExprT, Alts, 0, S).
constr_cases(Env, Switched, _SwitchedT, _ExprT, [], _N, S) ->
    [{unreachable, aeso_syntax:get_ann(Switched), Env}|S];
constr_cases(Env0, Switched, SwitchedT, ExprT,
             [{'case', Ann, Pat, Case}|Rest], N, S0) ->
    {EnvCase, EnvCont} = match_to_pattern(Env0, Pat, Switched, SwitchedT),
    {CaseDT, S1} = constr_expr(EnvCase, Case, S0),
    constr_cases(EnvCont, Switched, SwitchedT, ExprT, Rest,
                 [ {subtype, [{context, {switch, N}}|Ann], EnvCase, CaseDT, ExprT}
                 , {reachable, Ann, EnvCase}
                 | S1
                 ]
                ).

%% match_to_pattern computes
%%   - Env which will bind variables
%%   - Env which asserts that the match cannot succeed
-spec match_to_pattern(env(), pat(), expr(), type()) -> {env(), env()}.
match_to_pattern(Env0, Pat, Expr, Type) ->
    {Env1, Pred} = match_to_pattern(Env0, Pat, Expr, Type, []),
    EnvMatch = assert(Pred, Env1),
    EnvNoMatch =
        case Pred of
            [] -> assert(?bool(false), Env0);
            [H|T] ->
                PredExpr = lists:foldl(
                             fun(E, Acc) -> ?op(E, '&&', Acc)
                             end, H, T
                            ),
                assert(?op('!',  PredExpr), Env0)
        end,
    {EnvMatch, EnvNoMatch}.
match_to_pattern(Env, {typed, _, Pat, _}, Expr, Type, Pred) ->
    match_to_pattern(Env, Pat, Expr, Type, Pred);
match_to_pattern(Env, {id, _, "_"}, _Expr, _Type, Pred) ->
    {Env, Pred};
match_to_pattern(Env, Id = {id, _, _}, _Expr, Type, Pred) ->
    {bind_var(Id, Type, Env), Pred};
match_to_pattern(Env, _Pat, {id, _, "_"}, _Type, Pred) ->
    {Env, Pred}; % Useful in lists
match_to_pattern(Env, I = {int, _, _}, Expr, _Type, Pred) ->
    {Env, [?op(Expr, '==', I)|Pred]};
match_to_pattern(Env, {tuple, _, Pats}, Expr, {tuple_t, _, Types}, Pred) ->
    N = length(Pats),
    lists:foldl(
      fun({{Pat, PatT}, I}, {Env0, Pred0}) ->
              Ann = aeso_syntax:get_ann(Pat),
              Proj = {proj, Ann, Expr, ?tuple_proj_id(N, I)},
              match_to_pattern(Env0, Pat, Proj, PatT, Pred0)
      end,
      {Env, Pred}, lists:zip(lists:zip(Pats, Types), lists:seq(1, N))
     );
match_to_pattern(Env, {record, _, Fields}, Expr, {dep_record_t, _, Type, FieldsT}, Pred) ->
    FieldTypes =
        [{dep_field_t, Ann, Field, FieldT} || {{id, Ann, Field}, FieldT} <- FieldsT],
    Qid = case Type of
              {qid, _, _} -> Type;
              {app_t, _, Q, _} -> Q
          end,
    lists:foldl(
      fun({field, _, [{proj, _, Field}], Pat}, {Env0, Pred0}) ->
              PatT = proplists:get_value(name(Field), FieldTypes),
              Ann = aeso_syntax:get_ann(Pat),
              Proj = {proj, Ann, Expr, qid(qname(Qid) ++ [name(Field)])},
              match_to_pattern(Env0, Pat, Proj, PatT, Pred0)
      end,
      {Env, Pred}, Fields
     );
match_to_pattern(Env, QCon = {qcon, Ann, _},
                 Expr, DepT = {dep_variant_t, _, Type, _, _}, Pred0) ->
    %% This is for sure a nullary constructor
    match_to_pattern(Env, {app, Ann, ?typed(QCon, Type), []}, Expr, DepT, Pred0);
match_to_pattern(Env, {app, Ann, ?typed_p(QCon = {qcon, _, QName}), Args},
                 Expr, {dep_variant_t, _, _Type, _Tag, Constrs}, Pred0) ->
    N = length(Args),
    [Types] =
        [ ConArgs
         || {dep_constr_t, _, {con, _, CName}, ConArgs} <- Constrs,
            lists:last(QName) == CName
        ],
    Pred1 = [{is_tag, Ann, Expr, QCon, Types}|Pred0],
    lists:foldl(
      fun({{Arg, ArgT}, I}, {Env0, Pred}) ->
              ArgAnn = aeso_syntax:get_ann(Arg),
              Proj = {proj, ArgAnn, Expr, ?adt_proj_id(QCon, I)},
              match_to_pattern(Env0, Arg, Proj, ArgT, Pred)
      end,
      {Env, Pred1}, lists:zip(lists:zip(Args, Types), lists:seq(1, N))
     );
match_to_pattern(Env, {list, _, Pats}, Expr, {dep_list_t, _, ElemT, _}, Pred) ->
    N = length(Pats),
    lists:foldl(
      fun(Pat, {Env0, Pred0}) ->
              match_to_pattern(Env0, Pat, {id, ann(), "_"}, ElemT, Pred0)
      end,
      {Env, [?op(Expr, '==', ?int(N)) | Pred]}, Pats
     );
match_to_pattern(Env0, {app, _, {'::', _}, [H,T]}, Expr, {dep_list_t, TAnn, ElemT, _}, Pred0) ->
    Pred1 = [?op(Expr, '>', ?int(0))|Pred0],
    {Env1, Pred2} = match_to_pattern(Env0, H, {id, ann(), "_"}, ElemT, Pred1),
    match_to_pattern(Env1, T, {id, ann(), "_"},
                     {dep_list_t, TAnn, ElemT, [?op(length(), '==', ?op(Expr, '-', ?int(1)))]},
                     Pred2).

group_subtypes(Cs) ->
    Subts = [C || C = {subtype, _, _, _, {refined_t, _, _, _, {template, _, _}}} <- Cs],
    Rest = Cs -- Subts,

    SubtsMap =
        lists:foldl(
          fun ({subtype, Ann, Env,
                {refined_t, _, Id, _, SubQual},
                {refined_t, _, _, Base, {template, Subst, LV}}}, Map) ->
                  maps:put(LV, {Base, [{subtypes, Env, Ann, Id, Subst, SubQual}|element(2, maps:get(LV, Map, {{}, []}))]}, Map)
          end, #{}, Subts
         ),
    Rest ++ [ {subtype_group, Ts, Base, LV}
              || {LV, {Base, Ts}} <- maps:to_list(SubtsMap)
            ].


%% -- Substitution -------------------------------------------------------------

apply_subst({id, _, N}, {id, _, N}, In) ->
    In;
apply_subst({id, _, X}, Expr, {id, _, X}) ->
    Expr;
apply_subst({qid, _, X}, Expr, {qid, _, X}) ->
    Expr;
apply_subst({tvar, _, X}, Expr, {tvar, _, X}) ->
    Expr;
apply_subst({ltvar, X}, Expr, {ltvar, X}) ->
    Expr;
apply_subst(X, Expr, {template, S1, T}) ->
    {template, [{X, Expr}|S1], T};
apply_subst({id, _, Name}, _, T = {refined_t, _, {id, _, Name}, T, _}) ->
    T;
apply_subst(X, Expr, {refined_t, Ann, Id, T, Qual}) ->
    {refined_t, Ann, Id, T, apply_subst(X, Expr, Qual)};
apply_subst(X, Expr, {dep_fun_t, Ann, Args, RetT}) ->
    {dep_fun_t, Ann, apply_subst(X, Expr, Args),
     case X of
         {id, _, Name} ->
             case [{} || {dep_arg_t, _, {id, _, ArgName}, _} <- Args, ArgName =:= Name] of
                 [] -> apply_subst(X, Expr, RetT);
                 _ -> RetT
             end;
         _ -> apply_subst(X, Expr, RetT)
     end
    };
apply_subst(_X, _Expr, []) -> [];
apply_subst(X, Expr, [H|T]) -> [apply_subst(X, Expr, H)|apply_subst(X, Expr, T)];
apply_subst(X, Expr, T) when is_tuple(T) ->
    list_to_tuple(apply_subst(X, Expr, tuple_to_list(T)));
apply_subst(_X, _Expr, X) -> X.

apply_subst(Subs, Q) when is_map(Subs) ->
    apply_subst(maps:to_list(Subs), Q);
apply_subst(Subs, Q) when is_list(Subs) ->
    lists:foldl(fun({X, Expr}, Q0) -> apply_subst(X, Expr, Q0) end, Q, Subs).


%% -- Assignments --------------------------------------------------------------

cmp_qualifiers(SelfId, Thing) ->
    %% [].
    [ ?op(SelfId, '=<', Thing)
    , ?op(SelfId, '>=', Thing)
    , ?op(SelfId, '>', Thing)
    , ?op(SelfId, '<', Thing)
    ].

eq_qualifiers(SelfId, Thing) ->
    [ ?op(SelfId, '==', Thing)
    , ?op(SelfId, '!=', Thing)
    ].

int_qualifiers(SelfId, Thing) ->
    cmp_qualifiers(SelfId, Thing) ++ eq_qualifiers(SelfId, Thing).

plus_int_qualifiers(_, {int, _, 0}, _Thing) -> [];
plus_int_qualifiers(SelfId, Int, Thing) ->
    int_qualifiers(SelfId, ?op(Thing, '+', Int)) ++ int_qualifiers(SelfId, ?op(Thing, '-', Int)).

var_int_qualifiers(SelfId, Var) ->
    int_qualifiers(SelfId, Var) ++ plus_int_qualifiers(SelfId, ?int(1), Var).

inst_pred_variant_tag(SelfId, Qid, Constrs) ->
    [ {is_tag, ann(), SelfId, qcon(lists:droplast(qname(Qid)) ++ [name(Con)]), Args}
      || {constr_t, _, Con, Args} <- Constrs
    ] ++
    [ ?op('!', {is_tag, ann(), SelfId, qcon(lists:droplast(qname(Qid)) ++ [name(Con)]), Args})
      || {constr_t, _, Con, Args} <- Constrs
    ].

inst_pred_int(Env, SelfId) ->
    lists:concat(
      [ [Q || CoolInt <- Env#env.cool_ints,
              Q <- int_qualifiers(SelfId, ?int(CoolInt))
        ]
      , [ Q || {Var, {refined_t, _, _, ?int_tp, _}} <- maps:to_list(Env#env.var_env),
               Q <- var_int_qualifiers(SelfId, {id, ann(), Var})
        ]
      ]
     ).

inst_pred_bool(Env, SelfId) ->
    lists:concat(
      [ [Q || CoolBool <- [true, false],
              Q <- eq_qualifiers(SelfId, ?bool(CoolBool))
        ]
      , [ Q || {Var, {refined_t, _, _, ?bool_tp, _}} <- maps:to_list(Env#env.var_env),
               Q <- eq_qualifiers(SelfId, {id, ann(), Var})
        ]
      ]
     ).

inst_pred_tvar(Env, SelfId, TVar) ->
    [ Q || {Var, {refined_t, _, _, {tvar, _, TVar1}, _}} <- maps:to_list(Env#env.var_env),
           TVar == TVar1,
           Q <- eq_qualifiers(SelfId, {id, ann(), Var})
    ].

inst_pred(Env, SelfId, BaseT) ->
    case BaseT of
        ?int_tp ->
            inst_pred_int(Env, SelfId);
        ?bool_tp ->
            inst_pred_bool(Env, SelfId);
        {qid, _, _} ->
            case lookup_type(Env, BaseT) of
                {_, {[], {variant_t, Constrs}}} ->
                    inst_pred_variant_tag(SelfId, BaseT, Constrs);
                X -> error({todo, {inst_pred, X}})
            end;
        {app_t, _, {id, Ann, "list"}, _} ->
            inst_pred_int(Env, {id, Ann, "length"});
        {app_t, _, Qid = {qid, _, _}, Args} ->
            case lookup_type(Env, Qid) of
                {_, {AppArgs, {variant_t, Constrs}}} ->
                    inst_pred_variant_tag(
                      SelfId,
                      Qid,
                      apply_subst(lists:zip(Args, AppArgs), Constrs)
                     );
                X -> error({todo, {inst_pred, X}})
            end;
        {tvar, _, TVar} ->
            inst_pred_tvar(Env, SelfId, TVar);
        _ -> []
    end.

init_assg(Cs) ->
    lists:foldl(
      fun({well_formed, Env, {refined_t, _, Id, BaseT, {template, _, LV}}}, Acc) ->
              AllQs = inst_pred(Env, Id, BaseT),
              Acc#{LV => #ltinfo{id = Id, base = BaseT, env = Env, predicate = AllQs}};
         (_, Acc) -> Acc
      end, #{}, Cs).

assg_of(Assg, Var = {ltvar, _}) ->
    case maps:get(Var, Assg, undef) of
        undef -> error({undef_assg, Var});
        A -> A
    end.


apply_assg(Assg, Var = {ltvar, _}) ->
    case maps:get(Var, Assg, false) of
        #ltinfo{predicate = P} ->
            P;
        false -> []
    end;
apply_assg(Assg, {template, S, T}) ->
    apply_assg(Assg, apply_subst(S, T));
apply_assg(Assg, [H|T]) -> [apply_assg(Assg, H)|apply_assg(Assg, T)];
apply_assg(Assg, T) when is_tuple(T) ->
    list_to_tuple(apply_assg(Assg, tuple_to_list(T)));
apply_assg(_, X) -> X.


pred_of(Assg, Var = {ltvar, _}) ->
    (assg_of(Assg, Var))#ltinfo.predicate;
pred_of(_, P) when is_list(P)   ->
    P;
pred_of(Assg, {template, Subst, P}) ->
    apply_subst(Subst, pred_of(Assg, P));
pred_of(Assg, {refined_t, _, _, _, P}) ->
    pred_of(Assg, P);
pred_of(Assg, Env = #env{path_pred = PathPred}) ->
    ScopePred = type_binds_pred(Assg, type_binds(Env)),
    ScopePred ++ PathPred;
pred_of(_, _) ->
    [].

type_binds_pred(Assg, TB) ->
    type_binds_pred(Assg, fun(X) -> X end, TB).
type_binds_pred(Assg, Access, TB) ->
    [ Q
     || {Var, Type} <- TB,
        Q <- case Type of
                 {refined_t, _, Id, _, P} ->
                     apply_subst(Id, Access(Var), pred_of(Assg, P));
                 {tuple_t, _, Fields} ->
                     N = length(Fields),
                     type_binds_pred(
                       Assg,
                       fun(X) -> {proj, ann(), Access(Var), X} end,
                       lists:zip(
                         [?tuple_proj_id(N, I) || I <- lists:seq(1, N)],
                         Fields
                        )
                      );
                 {dep_record_t, _, RT, Fields} ->
                     QName = case RT of
                                 {qid, _, Q} -> Q;
                                 {app_t, _, {qid, _, Q}, _} -> Q
                             end,
                     type_binds_pred(
                       Assg,
                       fun(X) -> {proj, ann(), Access(Var), X} end,
                       [{qid(QName ++ [name(Field)]), T}
                        || {dep_field_t, _, Field, T} <- Fields]
                      );
                 {dep_variant_t, _, VT, Tag, Constrs} ->
                     QName = case VT of
                                 {qid, _, Q} -> Q;
                                 {app_t, _, {qid, _, Q}, _} -> Q
                             end,
                     TagPred = apply_subst(nu(), Access(Var), pred_of(Assg, Tag)),
                     ConPred =
                         lists:flatten(
                           [ type_binds_pred(
                               Assg,
                               fun(X) -> {proj, ann(), Access(Var), X} end,
                               lists:zip(
                                 [?adt_proj_id(qid(lists:droplast(QName) ++ [name(Con)]), I)
                                  || I <- lists:seq(1, length(Args))],
                                 Args
                              )
                              )
                             || {dep_constr_t, _, Con, Args} <- Constrs
                           ]),
                     TagPred ++ ConPred;
                 {dep_list_t, _, ElemT, LenPred} ->
                     type_binds_pred(Assg, Access, [ElemT]) ++
                         apply_subst(length(), Access(Var), pred_of(Assg, LenPred));
                 _ -> []
             end
    ].

simplify_assg(Assg) ->
    maps:map(fun(_K, V = #ltinfo{env = KEnv, id = Id, base = BaseType, predicate = Qs}) ->
                     ?DBG("SIMPLING: ~p :\n ~p", [Id, BaseType]),
                     V#ltinfo{
                       predicate =
                           simplify_pred(
                             Assg,
                             bind_var(Id, BaseType, KEnv),
                             Qs
                            )
                      }
             end, Assg).

%% -- Solving ------------------------------------------------------------------

split_constr(L) when is_list(L) ->
    split_constr(L, []).
split_constr([H|T], Acc) ->
    HC = split_constr1(H),
    split_constr(T, HC ++ Acc);
split_constr([], Acc) ->
    filter_obvious(Acc).

split_constr1(C = {subtype, Ann, Env0, SubT, SupT}) ->
    case {SubT, SupT} of
        { {dep_fun_t, _, ArgsSub, RetSub}
        , {dep_fun_t, _, ArgsSup, RetSup}
        } ->
            Contra =
                [ {subtype, Ann, Env0, ArgSupT, ArgSubT} %% contravariant!
                 || {{dep_arg_t, _, ArgSubT}, {dep_arg_t, _, ArgSupT}}
                        <- lists:zip(ArgsSub, ArgsSup)
                ],
            Env1 = bind_args(ArgsSup, Env0),
            Subst =
                [{Id1, Id2} || {{dep_arg_t, _, Id1, _}, {dep_arg_t, _, Id2, _}}
                                   <- lists:zip(ArgsSub, ArgsSup)],
            split_constr([{subtype, Ann, Env1, apply_subst(Subst, RetSub), RetSup}|Contra]);
        {{tuple_t, _, TSubs}, {tuple_t, _, TSups}} ->
            split_constr([{subtype, Ann, Env0, TSub, TSup} ||
                             {TSub, TSup} <- lists:zip(TSubs, TSups)]);
        { {dep_record_t, _, _, FieldsSub}
        , {dep_record_t, _, _, FieldsSup}
        } ->
            FieldsSub1 = lists:keysort(1, FieldsSub),
            FieldsSup1 = lists:keysort(1, FieldsSup),
            split_constr(
              [ {subtype, Ann, Env0, FTSub, FTSup}
               || {{dep_field_t, _, _, FTSub}, {dep_field_t, _, _, FTSup}} <- lists:zip(FieldsSub1, FieldsSup1)
              ]
             );
        { {dep_variant_t, _, TypeSub, TagSub, ConstrsSub}
        , {dep_variant_t, _, TypeSup, TagSup, ConstrsSup}
        } ->
            split_constr(
              [ {subtype, Ann, Env0, ?refined(TypeSub, TagSub), ?refined(TypeSup, TagSup)}
              | [ {subtype, Ann, Env0, ArgSub, ArgSup}
                 || { {dep_constr_t, _, _, ArgsSub}
                    , {dep_constr_t, _, _, ArgsSup}
                    } <- lists:zip(ConstrsSub, ConstrsSup),
                    {ArgSub, ArgSup} <- lists:zip(ArgsSub, ArgsSup)
                ]
              ]
             );
        { {dep_list_t, _, DepElemSub, LenQualSub}
        , {dep_list_t, _, DepElemSup, LenQualSup}
        } ->
            split_constr(
              [ {subtype, Ann, Env0, ?refined(?int_t, LenQualSub), ?refined(?int_t, LenQualSup)}
              , {subtype, Ann, Env0, DepElemSub, DepElemSup}
              ]
             );
        _ -> [C]
    end;
split_constr1(C = {well_formed, Env0, T}) ->
    case T of
        {dep_fun_t, _, Args, Ret} ->
            FromArgs =
                [ {well_formed, Env0, ArgT}
                  || {dep_arg_t, _, _, ArgT} <- Args
                ],
            Env1 = bind_args(Args, Env0),
            split_constr([{well_formed, Env1, Ret}|FromArgs]);
        {tuple_t, _, Ts} ->
            split_constr([{well_formed, Env0, Tt} || Tt <- Ts]);
        {dep_record_t, _, _, Fields} ->
            split_constr([{well_formed, Env0, TF} || {dep_field_t, _, _, TF} <- Fields]);
        {dep_variant_t, _, Type, Tag, Constrs} ->
            split_constr(
              [ {well_formed, Env0, ?refined(Type, Tag)}
              | [ {well_formed, Env0, Arg}
                  || {dep_constr_t, _, _, Args} <- Constrs,
                     Arg <- Args
                ]
              ]
             );
        {dep_list_t, _, DepElem, LenQual} ->
            [ {well_formed, Env0, ?refined(?int_t, LenQual)}
            , {well_formed, Env0, DepElem}
            ];
        _ -> [C]
    end;
split_constr1(C = {reachable, _, _}) ->
    [C];
split_constr1(C = {unreachable, _, _}) ->
    [C].

filter_obvious(L) ->
    filter_obvious(L, []).
filter_obvious([], Acc) ->
    Acc;
filter_obvious([H|T], Acc) ->
    case H of
        {well_formed, _, {refined_t, _, _, _, []}} ->
            filter_obvious(T, Acc);
         _ -> filter_obvious(T, [H|Acc])
    end.

-spec solve(env(), [constr()]) -> assignment().
solve(_Env, Cs) ->
    Assg0 = solve(init_assg(Cs), Cs, Cs),
    check_reachable(Assg0, Cs),
    simplify_assg(Assg0).
solve(Assg, _, []) ->
    Assg;
solve(Assg, AllCs, [C|Rest]) ->
    case valid_in(C, Assg) of
        false ->
            ?DBG("NOT VALID"),
            Weakened = weaken(C, Assg),
            solve(Weakened, AllCs, AllCs);
        true  ->
            ?DBG("VALID"),
            solve(Assg, AllCs, Rest)
    end.

valid_in({well_formed, _, _}, _) ->
    true;
valid_in({subtype_group, Subs, Base, SupPredVar}, Assg) ->
    Ltinfo = assg_of(Assg, SupPredVar),
    lists:all(
      fun({subtypes, Env, _, Id, Subst, SubPredVar}) ->
              SubPred = pred_of(Assg, SubPredVar),
              SupPred = apply_subst(Subst, pred_of(Assg, SupPredVar)),
              AssumpPred = apply_subst(Id, Ltinfo#ltinfo.id, SubPred),
              ConclPred = SupPred,
              ?DBG("COMPLEX SUBTYPE ON ~s and ~s\n~s\n<:\n~s",
                   [name(Id), name(Ltinfo#ltinfo.id),
                    aeso_pretty:pp(predicate, SubPred),
                    aeso_pretty:pp(predicate, SupPred)
                   ]
                  ),
              Env1 = bind_var(Ltinfo#ltinfo.id, Base, Env),
              impl_holds(Assg, Env1, AssumpPred, ConclPred)
      end,
      Subs
     );
valid_in({subtype, Ann, Env,
          {refined_t, _, SubId, _, SubP}, {refined_t, _, SupId, Base, SupP}}, Assg) when is_list(SupP) ->
    ?DBG("RIGID SUBTYPE\n~p\n<:\n~p", [SubP, SupP]),
    SubPred = pred_of(Assg, SubP),
    SupPred = pred_of(Assg, SupP),
    AssumpPred = apply_subst(SubId, SupId, SubPred),
    ConclPred  = SupPred,
    Env1 = ensure_var(SupId, Base, Env),
    case impl_holds(Assg, Env1, AssumpPred, ConclPred) of
        true ->
            true;
        false ->
            ?DBG("**** CONTRADICTION"),
            SimpAssump = simplify_pred(Assg, Env1, pred_of(Assg, Env1) ++ AssumpPred),
            throw({contradict, {Ann, SimpAssump, ConclPred}})
    end;
valid_in(C = {subtype, _, _, _, _}, _) -> %% We trust the typechecker
    ?DBG("SKIPPING SUBTYPE: ~s", [aeso_pretty:pp(constr, C)]),
    true;
valid_in(_, _) ->
    true.


weaken({subtype_group, Subs, Base, SupPredVar}, Assg) ->
    ?DBG("WEAKENING"),
    Ltinfo = assg_of(Assg, SupPredVar),
    Filtered =
        [ Q || Q <- Ltinfo#ltinfo.predicate,
               lists:all(fun({subtypes, Env, _, Id, Subst, Sub}) ->
                                 SubPred = pred_of(Assg, Sub),
                                 AssumpPred = apply_subst(Id, Ltinfo#ltinfo.id, SubPred),
                                 ConclPred  = apply_subst(Subst, Q),
                                 Env1 = bind_var(Ltinfo#ltinfo.id, Base, Env),
                                 impl_holds(Assg, Env1, AssumpPred, ConclPred)
                         end, Subs)
        ],
    NewLtinfo = Ltinfo#ltinfo{
                 predicate = Filtered
                },
    ?DBG("WEAKENED FROM\n~s\nTO\n~s", [aeso_pretty:pp(predicate, Ltinfo#ltinfo.predicate),
                                       aeso_pretty:pp(predicate, Filtered)
                                      ]),
    Assg#{SupPredVar => NewLtinfo};
weaken({well_formed, _Env, {refined_t, _, _, _, _}}, Assg) ->
    Assg.

check_reachable(Assg, [{reachable, Ann, Env}|Rest]) ->
    case impl_holds(Assg, Env, [], [?bool(false)]) of
        true -> throw({valid_unreachable, {Ann, Env}});
        false -> check_reachable(Assg, Rest)
    end;
check_reachable(Assg, [{unreachable, Ann, Env}|Rest]) ->
    case impl_holds(Assg, Env, [], [?bool(false)]) of
        true -> check_reachable(Assg, Rest);
        false -> throw({invalid_reachable, {Ann, Env}})
    end;
check_reachable(Assg, [_|Rest]) ->
    check_reachable(Assg, Rest);
check_reachable(_, []) ->
    ok.


%% -- SMT Solving --------------------------------------------------------------

declare_tuples([]) ->
    ok;
declare_tuples([N|Rest]) ->
    Seq = lists:seq(1, N),
    aeso_smt:send_z3_success(
      {app, "declare-datatypes",
       [{list, [{var, "T" ++ integer_to_list(I)}
                || I <- Seq
               ]},
        {list, [{app, "$tuple" ++ integer_to_list(N),
                 [{app, "$mk_tuple" ++ integer_to_list(N),
                   [{app, name(?tuple_proj_id(N, I)), [{var, "T" ++ integer_to_list(I)}]}
                    || I <- Seq
                   ]
                  }
                 ]
                }
               ]}
       ]
      }
     ),
    declare_tuples(Rest).

%% TODO fix this disgusting shit
declare_datatypes([]) ->
    ok;
declare_datatypes([{Name, {Args, TDef}}|Rest]) ->
    TName = string:join(qname(Name), "."),
    TypeSubst = [{Arg, fresh_id("t")} || Arg <- Args],
    SMTArgs = [T || {_, T} <- TypeSubst],
    case TDef of
        {alias_t, _} -> ok;
        {record_t, Fields} ->
            aeso_smt:send_z3_success(
              {app, "declare-datatypes",
               [{list, [type_to_smt(A) || A <- SMTArgs]},
                 {list, [{app, TName,
                         [{app, "$mk_" ++ TName,
                           [{app, TName ++ "." ++ name(FName),
                             [type_to_smt(apply_subst(TypeSubst, T))]}
                            || {field_t, _, FName, T} <- Fields
                           ]
                          }
                         ]
                        }
                       ]}
                ]
              }
             );
        {variant_t, Constrs} ->
            aeso_smt:send_z3_success(
              {app, "declare-datatypes",
               [{list, [type_to_smt(A) || A <- SMTArgs]},
                {list, [ {app, TName,
                          [ begin
                                QualCon = lists:droplast(qname(Name)) ++ [name(Con)],
                                ConName = string:join(QualCon, "."),
                                {app, ConName,
                                 [{app, name(?adt_proj_id(qid(QualCon), I)),
                                   [type_to_smt(apply_subst(TypeSubst, T))]}
                                  || {T, I} <-
                                         lists:zip(
                                           ConArgs,
                                           lists:seq(1, length(ConArgs))
                                          )
                                 ]
                                }
                            end
                            || {constr_t, _, Con, ConArgs} <- Constrs
                         ]
                        }
                       ]}
               ]
              }
             )
    end,
    declare_datatypes(Rest).

declare_type_binds(Assg, Env) ->
    ?DBG("TB: ~p", [type_binds(Env)]),
    [ begin
          aeso_smt:declare_const(expr_to_smt(Var), type_to_smt(T))
      end
      || {Var, T} <- type_binds(Env), element(1, T) =/= dep_fun_t,
         is_smt_expr(Var),
         is_smt_type(T)
    ],
    [ aeso_smt:assert(expr_to_smt(Q))
     || Q <- pred_of(Assg, Env)
    ].

impl_holds(Env, Assump, Concl) ->
    impl_holds(#{}, Env, Assump, Concl).
impl_holds(Assg, Env, Assump, Concl) when not is_list(Assump) ->
    impl_holds(Assg, Env, [Assump], Concl);
impl_holds(Assg, Env, Assump, Concl) when not is_list(Concl) ->
    impl_holds(Assg, Env, Assump, [Concl]);
impl_holds(_, _, _, []) -> true;
impl_holds(Assg, Env, Assump, Concl) ->
    ConclExpr  = {app, ann(), {'&&', ann()}, Concl}, %% Improper Sophia expr but who cares
    %% ?DBG("IMPL;\n* ASSUMPTION: ~s\n* CONCLUSION: ~s",
    %%      [ string:join([aeso_pretty:pp(expr, E)|| E <- Assump], " && ")
    %%      , string:join([aeso_pretty:pp(expr, E)|| E <- Concl],  " && ")
    %%      ]),
    aeso_smt:scoped(
      fun() ->
              declare_type_binds(Assg, Env),
              [ aeso_smt:assert(expr_to_smt(Expr))
                || Expr <- Assump
              ],
              aeso_smt:assert(expr_to_smt(?op('!', ConclExpr))),
              case aeso_smt:check_sat() of
                  {error, Err} -> throw({smt_error, Err});
                  Res ->
                      %% case Res of
                      %%     true -> ?DBG("FALSE");
                      %%     false  -> ?DBG("HOLDS")
                      %% end,
                      not Res
              end
      end).


is_smt_type(Expr) ->
    try type_to_smt(Expr) of
        _ -> true
    catch throw:{not_smt_type, _} ->
            false
    end.

type_to_smt({refined_t, _, _, T, _}) ->
    type_to_smt(T);
type_to_smt(?bool_tp) ->
    {var, "Bool"};
type_to_smt(?int_tp) ->
    {var, "Int"};
type_to_smt({id, _, "string"}) ->
    {var, "Int"};
type_to_smt({id, _, I}) ->
    {var, I};
type_to_smt({tvar, _, _}) ->
    {var, "Int"}; % lol
type_to_smt({qid, _, QVar}) ->
    {var, string:join(QVar, ".")};
type_to_smt(?tuple_tp(Types)) ->
    N = length(Types),
    {app, "$tuple" ++ integer_to_list(N),
     [type_to_smt(T) || T <- Types]
    };
type_to_smt({dep_record_t, _, T, _}) ->
    type_to_smt(T);
type_to_smt({dep_variant_t, _, T, _, _}) ->
    type_to_smt(T);
type_to_smt({dep_list_t, _, _, _}) ->
    {var, "Int"};  % Lists are yet lengths
type_to_smt({app_t, _, {id, _, "list"}, _}) ->
    {var, "Int"}; % Lists are yet lengths
type_to_smt({app_t, _, T, Args}) ->
    {var, T1} = type_to_smt(T),
    {app, T1, lists:map(fun type_to_smt/1, Args)};
type_to_smt(T) ->
    ?DBG("NOT SMT TYPE ~p", [T]),
    throw({not_smt_type, T}).

is_smt_expr(Expr) ->
    try expr_to_smt(Expr) of
        _ -> true
    catch throw:{not_smt_expr, _} ->
            false
    end.

expr_to_smt({id, _, Var}) ->
    {var, lists:flatten(string:replace(Var, "#", "$", all))};
expr_to_smt({con, _, Var}) ->
    {var, Var};
expr_to_smt({qid, _, QVar}) ->
    {var, string:join(QVar, ".")};
expr_to_smt({qcon, _, QVar}) ->
    {var, string:join(QVar, ".")};
expr_to_smt({bool, _, true}) ->
    {var, "true"};
expr_to_smt({bool, _, false}) ->
    {var, "false"};
expr_to_smt({int, _, I}) ->
    {int, I};
expr_to_smt({string, _, S}) ->
    %% FIXME this sucks as it doesn't play well with the concatenation
    {int, binary:decode_unsigned(crypto:hash(md5, S))};
expr_to_smt({typed, _, E, _}) ->
    expr_to_smt(E);
expr_to_smt(E = {app, _, F, Args}) ->
    case expr_to_smt(F) of
        {var, Fun} ->
            {app, Fun, [expr_to_smt(Arg) || Arg <- Args]};
        _ -> throw({not_smt_expr, E})
    end;
expr_to_smt({proj, Ann, E, Field}) ->
    expr_to_smt({app, Ann, Field, [E]});
expr_to_smt({is_tag, _, What, QCon, []}) ->
    {app, "=",
     [ expr_to_smt(What)
     , {var, string:join(qname(QCon), ".")}
     ]
    };
expr_to_smt({is_tag, _, What, QCon, Args}) ->
    N = length(Args),
    MakeArg = fun(I) -> {var, "$arg" ++ integer_to_list(I)}
              end,
    {app, "exists",
     [ {list,
        [ {list, [ MakeArg(I), type_to_smt(ArgT)]}
          || {ArgT, I} <- lists:zip(Args, lists:seq(1, N))
        ]
       }
     , {app, "=",
        [ expr_to_smt(What)
        , {app, string:join(qname(QCon), "."),
           [MakeArg(I) || I <- lists:seq(1, N)]
          }
        ]
       }
     ]
    };
expr_to_smt({'&&', _}) -> {var, "&&"};
expr_to_smt({'||', _}) -> {var, "||"};
expr_to_smt({'=<', _}) -> {var, "<="};
expr_to_smt({'>=', _}) -> {var, ">="};
expr_to_smt({'==', _}) -> {var, "="};
expr_to_smt({'!=', _}) -> {var, "distinct"};
expr_to_smt({'<', _})  -> {var, "<"};
expr_to_smt({'>', _})  -> {var, ">"};
expr_to_smt({'+', _})  -> {var, "+"};
expr_to_smt({'-', _})  -> {var, "-"};
expr_to_smt({'*', _})  -> {var, "*"};
expr_to_smt({'/', _})  -> {var, "div"};
expr_to_smt({'!', _})  -> {var, "not"};
expr_to_smt({'^', _})  -> {var, "^"};
expr_to_smt({'mod', _})  -> {var, "mod"};
expr_to_smt(E) -> ?DBG("NOT SMT EXPR ~p", [E]), throw({not_smt_expr, E}).


%% -- Simplification -----------------------------------------------------------

flip_op('>') ->
    '<';
flip_op('<') ->
    '>';
flip_op('>=') ->
    '=<';
flip_op('=<') ->
    '>=';
flip_op('==') ->
    '==';
flip_op('!=') ->
    '!=';
flip_op('+') ->
    '+';
flip_op('*') ->
    '*';
flip_op(_) ->
    no_flip.

sort_preds_by_meaningfulness(Preds0) ->
    Preds1 = %% Move nu to the left side if it makes sense
        [ case {R, flip_op(Op)} of
              {?nu_p, FlipOp} when FlipOp =/= no_flip ->
                  {app, Ann, {FlipOp, OpAnn}, [R, L]};
              _ -> Q
          end
         || Q = {app, Ann, {Op, OpAnn}, [L, R]} <- Preds0
        ],
    Preds2 = lists:usort(Preds1),
    OpList =
        lists:zip(lists:reverse(['==', '>', '<', '>=', '=<', '!=']), lists:seq(1, 6)),
    Cmp = fun ({app, _, {OpL, _}, [LL, LR]}, {app, _, {OpR, _}, [RL, RR]}) ->
                  SimplBonus = fun SB(?nu_p)        -> 1000000000000000;
                                   SB({int, _, I})  -> 100000 - abs(I);
                                   SB({bool, _, _}) -> 10000;
                                   SB({id, _, _})   -> 1000;
                                   SB({qid, _, _})  -> 100;
                                   SB({app, _, _, _}) -> -10000000000;
                                   SB({typed, _, E, _}) -> SB(E);
                                   SB(_) -> 0
                               end,
                  ValueL = proplists:get_value(OpL, OpList, 0) * 1000000 + SimplBonus(LL) + SimplBonus(LR),
                  ValueR = proplists:get_value(OpR, OpList, 0) * 1000000 + SimplBonus(RL) + SimplBonus(RR),
                  ValueL =< ValueR;
              (_, _) -> true
          end,
    TagPreds = [P || P <- Preds0, element(1, P) == is_tag],
    lists:sort(Cmp, Preds2) ++ TagPreds.

%% this is absolutely heuristic
simplify_pred(Assg, Env, Pred) ->
    %% ?DBG("*** SIMPLIFY PRED"),
    case impl_holds(Assg, Env, Pred, [{bool, ann(), false}]) of
        true -> [{bool, ann(), false}];
        false -> simplify_pred(Assg, Env, [], sort_preds_by_meaningfulness(Pred))
    end.
simplify_pred(_Assg, _Env, Prev, []) ->
    Prev;
simplify_pred(Assg, Env, Prev, [Q|Post]) ->
    case impl_holds(Assg, Env, Prev ++ Post, Q) of
        true ->
            simplify_pred(Assg, Env, Prev, Post);
        false ->
            simplify_pred(Assg, Env, [Q|Prev], Post)
    end.


%% -- A-Normalization ----------------------------------------------------------

%% A-Normalization – No compound expr may consist of compound exprs
a_normalize(Expr = {typed, Ann, _, Type}) ->
    {Expr1, Decls} = a_normalize(Expr, []),
    case Decls of
        [] -> Expr1;
        _ -> ?typed({block, Ann, lists:reverse([Expr1|Decls])}, Type)
    end.

a_normalize({typed, _, Expr, Type}, Decls) ->
    a_normalize(Expr, Type, Decls);
a_normalize(Expr = {Op, _}, Decls) when is_atom(Op) ->
    {Expr, Decls};
a_normalize(L, Decls) when is_list(L) ->
    a_normalize_list(L, [], Decls).

a_normalize({app, Ann, Fun, Args}, Type, Decls0) ->
    {Fun1,  Decls1} = a_normalize_to_simpl(Fun, Decls0),
    {Args1, Decls2} = a_normalize_to_simpl(Args, Decls1),
    {?typed({app, Ann, Fun1, Args1}, Type),
     Decls2
    };
a_normalize({'if', Ann, Cond, Then, Else}, Type, Decls0) ->
    {Cond1, Decls1} = a_normalize_to_simpl(Cond, Decls0),
    Then1 = a_normalize(Then),
    Else1 = a_normalize(Else),
    {?typed({'if', Ann, Cond1, Then1, Else1}, Type),
     Decls1
    };
a_normalize({switch, Ann, Expr, Alts}, Type, Decls0) ->
    {Expr1, Decls1} = a_normalize_to_simpl(Expr, Decls0),
    Alts1 =
        [ {'case', CAnn, Pat, a_normalize(CaseExpr)}
          || {'case', CAnn, Pat, CaseExpr} <- Alts
        ],
    {?typed({switch, Ann, Expr1, Alts1}, Type),
     Decls1
    };
a_normalize({lam, Ann, Args, Body}, Type, Decls0) ->
    Body1 = a_normalize(Body),
    {?typed({lam, Ann, Args, Body1}, Type),
     Decls0
    };
a_normalize({tuple, Ann, Elems}, Type, Decls0) ->
    {Elems1, Decls1} = a_normalize_to_simpl_list(Elems, [], Decls0),
    {?typed({tuple, Ann, Elems1}, Type),
     Decls1
    };
a_normalize({record, Ann, FieldVals}, Type, Decls0) ->
    Vals = [Val || {field, _, _, Val} <- FieldVals],
    {Vals1, Decls1} = a_normalize_to_simpl_list(Vals, [], Decls0),
    {?typed({record, Ann,
             [{field, FAnn, Field, Val}
              || {Val, {field, FAnn, Field, _}} <- lists:zip(Vals1, FieldVals)]
            }, Type),
     Decls1
    };
a_normalize({proj, Ann, Expr, Field}, Type, Decls0) ->
    {Expr1, Decls1} = a_normalize_to_simpl(Expr, Decls0),
    {?typed({proj, Ann, Expr1, Field}, Type),
     Decls1
    };
a_normalize({list, Ann, Elems}, Type, Decls0) ->
    {Elems1, Decls1} = a_normalize_to_simpl_list(Elems, [], Decls0),
    {?typed({list, Ann, Elems1}, Type),
     Decls1
    };
a_normalize({block, Ann, Stmts}, Type, Decls0) ->
    {Stmts1, Decls1} = a_normalize(Stmts, Decls0),
    {?typed({block, Ann, Stmts1}, Type),
     Decls1
    };
a_normalize(Expr, Type, Decls) ->
    {?typed(Expr, Type),
     Decls
    }.

a_normalize_list([], Acc, Decls) ->
    {lists:reverse(Acc), Decls};
a_normalize_list([{letval, Ann, Pat, Body}|Rest], Acc, Decls0) ->
    {Body1, Decls1} = a_normalize(Body, Decls0),
    a_normalize_list(Rest, Acc, [{letval, Ann, Pat, Body1}|Decls1]);
a_normalize_list([{letfun, Ann, Name, Args, RetT, Body}|Rest], Acc, Decls0) ->
    a_normalize_list(Rest, Acc, [{letfun, Ann, Name, Args, RetT, a_normalize(Body)}|Decls0]);
a_normalize_list([Expr|Rest], Acc, Decls0) ->
    {Expr1, Decls1} = a_normalize(Expr, Decls0),
    a_normalize_list(Rest, [Expr1|Acc], Decls1).


a_normalize_to_simpl({typed, _, Expr, Type}, Decls) ->
    a_normalize_to_simpl(Expr, Type, Decls);
a_normalize_to_simpl(Expr = {Op, _}, Decls) when is_atom(Op) ->
    {Expr, Decls};
a_normalize_to_simpl(L, Decls) when is_list(L) ->
    a_normalize_to_simpl_list(L, [], Decls).


a_normalize_to_simpl(Expr = {id, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {qid, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {con, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {qcon, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {int, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {bool, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {string, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {Op, _}, Type, Decls) when is_atom(Op) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr, Type, Decls0) ->
    {Expr1, Decls1} = a_normalize(Expr, Type, Decls0),
    Var = fresh_id("anorm_" ++ atom_to_list(element(1, Expr)), Type),
    {Var,
     [{letval, ann(), Var, Expr1}|Decls1]
    }.

a_normalize_to_simpl_list([], Acc, Decls) ->
    {lists:reverse(Acc), Decls};
a_normalize_to_simpl_list([{letval, Ann, Pat, Body}|Rest], Acc, Decls0) ->
    {Body1, Decls1} = a_normalize_to_simpl(Body, Decls0),
    a_normalize_to_simpl_list(Rest, Acc, [{letval, Ann, Pat, Body1}|Decls1]);
a_normalize_to_simpl_list([Expr|Rest], Acc, Decls0) ->
    {Expr1, Decls1} = a_normalize_to_simpl(Expr, Decls0),
    a_normalize_to_simpl_list(Rest, [Expr1|Acc], Decls1).
