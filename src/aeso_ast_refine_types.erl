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

-define(refined(T), {refined_t, element(2, T), T, []}).
-define(refined(T, Q), {refined_t, element(2, T), T, Q}).
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
%% -define(string_tp, {id, _, "string"}).
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

%% Liquid type, possibly uninstantiated
-type lutype() :: dep_type( predicate() | template() ).

-type fun_env() :: #{name() => template()}.
-type var_env() :: #{name() => template()}.
-type type_env() :: #{name() => typedef()}.

-record(scope, { fun_env = #{} :: fun_env()
               , type_env = #{} :: type_env()
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
-type subtype_group() :: {subtype_group, [{env(), ann(), subst(), lutype()}], type(), ltvar()}.

%% Constraint
-type constr() :: {subtype, ann(), env(), lutype(), lutype()}
                | subtype_group()
                | {well_formed, env(), lutype()}
                | {reachable, ann(), env()}
                | {unreachable, ann(), env()}.

%% Information about ltvar
-record(ltinfo, {base :: type(), predicate :: predicate(), env :: env()}).
-type ltinfo() :: #ltinfo{}.

%% Predicate assignment
-type assignment() :: #{name() => ltinfo()}.

%% Position in type
-type variance() :: contravariant | covariant | forced_covariant | forced_contravariant.

-spec ann() -> ann().
ann() -> [{origin, hagia}].
-spec ann(ann()) -> ann().
ann(L) -> [{origin, hagia}|L].

nu() ->
    {id, ann(), "$nu"}.
-define(nu_p, {id, _, "$nu"}).

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

qcon(X) ->
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
            ?DBG("SHADOW OF ~p : ~p IN\n~p", [Id, V, VarEnv]),
            throw({overwrite, Id})
    end,
    Env#env{ var_env = VarEnv#{name(Id) => T}}.

-spec bind_nu(lutype(), env()) -> env().
bind_nu(Type, Env) ->
    bind_var(nu(), Type, Env).

-spec bind_vars([{id(), lutype()}], env()) -> env().
bind_vars([], Env) -> Env;
bind_vars([{X, T} | Vars], Env) ->
    bind_vars(Vars, bind_var(X, T, Env)).

-spec bind_fun(name(), lutype(), env()) -> env().
bind_fun(X, Type, Env) ->
    on_current_scope(Env, fun(Scope = #scope{ fun_env = Funs }) ->
                                  Scope#scope{ fun_env = Funs#{X => Type} }
                          end).

-spec bind_funs([{name(), lutype()}], env()) -> env().
bind_funs([], Env) -> Env;
bind_funs([{Id, Type} | Rest], Env) ->
    bind_funs(Rest, bind_fun(Id, Type, Env)).

-spec bind_type(id(), [type()], typedef(), env()) -> env().
bind_type(Id, Args, Def, Env) ->
    on_current_scope(Env, fun(Scope = #scope{ type_env = Types }) ->
                                  Scope#scope{ type_env = Types#{Id => {Args, Def}} }
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
            Defs = case Kind of
                       term -> Funs;
                       type -> Types
                   end,
            case maps:get(Name, Defs, false) of
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

-spec type_binds(env()) -> [{expr(), lutype()}].
type_binds(#env{var_env = VEnv, scopes = Scopes}) ->
    [ {qid([Var]), Type}
      || {Var, Type} <- maps:to_list(VEnv)
    ] ++
        [ {qid(ScopePath ++ [Var]), Type}
          || {ScopePath, #scope{fun_env = FEnv}} <- maps:to_list(Scopes),
             {Var, Type} <- maps:to_list(FEnv)
        ].

-spec type_defs(env()) -> [{qid(), typedef()}]. %% FIXME really typedef? what about args?
type_defs(#env{scopes = Scopes}) ->
    [ {qid(ScopePath ++ [Var]), TypeDef}
      || {ScopePath, #scope{type_env = TEnv}} <- maps:to_list(Scopes),
         {Var, TypeDef} <- maps:to_list(TEnv)
    ].

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
    DFun    = fun(Ts, T) -> {dep_fun_t, Ann, [], Ts, T} end,
    DFun1   = fun(S, T) -> DFun([S], T) end,
    %% Lambda    = fun(Ts, T) -> {fun_t, Ann, [], Ts, T} end,
    %% Lambda1   = fun(S, T) -> Lambda([S], T) end,
    StateDFun  = fun(Ts, T) -> {dep_fun_t, [stateful|Ann], [], Ts, T} end,

    MkDefs = fun maps:from_list/1,

    ChainScope = #scope
        { fun_env = MkDefs(
                     %% Spend transaction.
                    [{"spend",        StateDFun([{id("addr"), Address}, {id("amount"), ?d_nonneg_int}], Unit)},
                     %% Chain environment
                     {"balance",      DFun1({id("addr"), Address}, ?d_nonneg_int)},
                     {"block_hash",   DFun1({id("h"), ?d_nonneg_int}, Option(Hash))},
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
                     [{"length",  DFun1({id("str"), String}, ?d_nonneg_int)}])
        },

    %% Bits
    BitsScope = #scope
        { fun_env = MkDefs(
                     [{"set",          DFun([{id("bits"), Bits}, ?d_nonneg_int], Bits)},
                      {"clear",        DFun([{id("bits"), Bits}, ?d_nonneg_int], Bits)},
                      {"test",         DFun([{id("bits"), Bits}, ?d_nonneg_int], Bool)},
                      {"sum",          DFun1({id("bits"), Bits}, ?d_nonneg_int)}])
                     },

    %% Bytes
    BytesScope = #scope
        { fun_env = MkDefs(
                   [{"to_int", DFun1({id("bytes"), Bytes(any)}, ?d_nonneg_int)}]) },

    TopScope = #scope
        { fun_env  = MkDefs(
                    [])
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
find_cool_ints([H|T], Acc) ->
    find_cool_ints(T, find_cool_ints(H, Acc));
find_cool_ints(T, Acc) when is_tuple(T) ->
    find_cool_ints(tuple_to_list(T), Acc);
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

-spec bind_ast_funs(ast(), env()) -> env().
bind_ast_funs(AST, Env) ->
    lists:foldr(
      fun({HEAD, _, Con, Defs}, Env0)
            when HEAD =:= namespace orelse HEAD =:= contract orelse HEAD =:= contract_main ->
              Env1 = push_scope(Con, Env0),
              Env2 = bind_funs(
                       [ begin
                             ArgsT =
                                 [ {ArgName, fresh_liquid(Env1, contravariant, "arge_" ++ StrName, T)}
                                   || ?typed_p(ArgName = {id, _, StrName}, T) <- Args
                                 ],
                             TypeDep = {dep_fun_t, FAnn, [], ArgsT, fresh_liquid(Env1, "rete", RetT)},
                             {Name, TypeDep}
                         end
                         || {letfun, FAnn, {id, _, Name}, Args, RetT, _} <- Defs
                       ],
                       Env1),
              Env3 = pop_scope(Env2),
              Env3
      end,
     Env, AST).


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

%% Decorates base types with templates through the AST
-spec fresh_liquid(env(), name(), term()) -> term().
fresh_liquid(Env, Hint, Type) ->
    fresh_liquid(Env, covariant, Hint, Type).

-spec fresh_liquid(env(), name(), variance(), term()) -> term().
fresh_liquid(_Env, Variance, Hint, Type = {id, Ann, _}) ->
    {refined_t, Ann, Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {con, Ann, _}) ->
    {refined_t, Ann, Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {qcon, Ann, _}) ->
    {refined_t, Ann, Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {tvar, Ann, _}) ->
    {refined_t, Ann, Type, fresh_template(Variance, Hint)};
fresh_liquid(Env, Variance, Hint, Type = {qid, Ann, _}) ->
    case lookup_type(Env, Type) of
        false ->
            error({undefined_type, Type});
        {QName, TDef} ->
            case TDef of
                {[], {alias_t, Type1}} ->
                    fresh_liquid(Env, Variance, Hint, Type1);
                {[], {record_t, Fields}} ->
                    {dep_record_t, Ann,
                     qid(QName),
                     [ {Field, fresh_liquid(Env, Variance, Hint ++ "_" ++ name(Field), FType)}
                      || {field_t, _, Field, FType} <- Fields
                     ]
                    };
                {[], {variant_t, Constrs}} ->
                    DepConstrs =
                        [ {dep_constr_t, CAnn, Con,
                           fresh_liquid(Env, Variance, Hint ++ "_" ++ name(Con), Vals)}
                          || {constr_t, CAnn, Con, Vals} <- Constrs
                        ],
                    {dep_variant_t, Ann, Type, fresh_template(Variance, Hint ++ "_tag"), DepConstrs}
            end
    end;
fresh_liquid(Env, Variance, Hint, {fun_t, Ann, Named, Args, Ret}) ->
    { dep_fun_t, Ann, Named
    , [{fresh_id("argt"),
        fresh_liquid(Env, switch_variance(Variance), Hint ++ "_argtt", Arg)}
       || Arg <- Args]
    , fresh_liquid(Env, Variance, Hint, Ret)
    };
fresh_liquid(Env, Variance, Hint, {tuple_t, Ann, Types}) ->
    {dep_tuple_t, Ann, fresh_liquid(Env, Variance, Hint, Types)};
fresh_liquid(_Env, _, _, []) -> [];
fresh_liquid(Env, Variance, Hint, [H|T]) ->
    [fresh_liquid(Env, Variance, Hint, H)|fresh_liquid(Env, Variance, Hint, T)];
fresh_liquid(Env, Variance, Hint, T) when is_tuple(T) ->
    list_to_tuple(fresh_liquid(Env, Variance, Hint, tuple_to_list(T)));
fresh_liquid(_Env, _, _, X) -> X.

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

refine_ast(AST) ->
    Env0 = init_env(),
    Env1 = with_cool_ints_from(AST, Env0),
    Env2 = register_typedefs(AST, Env1),
    Env3 = bind_ast_funs(AST, Env2),
    {AST1, CS0} = constr_ast(Env3, AST),
    CS1 = split_constr(CS0),
    CS2 = group_subtypes(CS1),
    try aeso_smt:scoped(
          fun() ->
                  declare_tuples(find_tuple_sizes(AST)),
                  declare_datatypes(type_defs(Env3)),
                  solve(Env3, CS2)
          end) of
        Assg ->
            AST2 = apply_assg(Assg, AST1),
            {ok, AST2}
    catch {ErrType, _}=E
                when ErrType =:= contradict
                     orelse ErrType =:= invalid_reachable
                     orelse ErrType =:= valid_unreachable
                     orelse ErrType =:= overwrite
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
  when Tag =:= contract orelse Tag =:= namespace ->
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
constr_letfun(Env0, {letfun, Ann, Id = {id, _, Name}, Args, RetT, Body}, S0) ->
    ArgsT =
        [ {ArgId, fresh_liquid(Env0, contravariant, "argi_" ++ ArgName, T)}
          || ?typed_p(ArgId = {id, _, ArgName}, T) <- Args
        ],
    Env1 = bind_vars(ArgsT, Env0),
    Body1 = a_normalize(Body),
    ?DBG("NORMALIZED\n~s\nTO\n~s", [aeso_pretty:pp(expr, Body), aeso_pretty:pp(expr, Body1)]),
    DepRetT = fresh_liquid(Env0, "ret_" ++ Name, RetT),
    {BodyT, S1} = constr_expr(Env1, Body1, S0),
    DepSelfT =
        { dep_fun_t, Ann, []
        , ArgsT
        , DepRetT
        },
    {_, GlobalFunType} = type_of(Env1, Id),
    S3 = [ {subtype, Ann, Env0, DepSelfT, GlobalFunType}
         , {subtype, Ann, Env1, BodyT, DepRetT}
         , {well_formed, Env0, GlobalFunType}
         , {well_formed, Env0, DepSelfT}
         | S1
         ],

    {{fun_decl, Ann, Id, DepSelfT}, S3}.

register_typedefs([{Tag, _, Con, Defs}|Rest], Env0)
  when Tag =:= contract orelse Tag =:= namespace ->
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

constr_expr(Env, ?typed_p({app, Ann, F, Args}, RetT), S)
  when element(1, F) =/= typed ->
    ArgTypes = [ArgT || {typed, _, _, ArgT} <- Args],
    TypedF = {typed, Ann, F, {fun_t, Ann, ann(), ArgTypes, RetT}},
    constr_expr(Env, ?typed({app, Ann, TypedF, Args}, RetT), S);
constr_expr(Env, ?typed_p(Expr, T), S) ->
    constr_expr(Env, Expr, T, S);
constr_expr(_, X, _) ->
    error({untyped, X}).

constr_expr(Env, {block, _, Stmts}, T, S) ->
    constr_expr(Env, Stmts, T, S);
constr_expr(Env, {typed, _, E, T1}, T2, S) ->
    case T1 == T2 of
        true -> constr_expr(Env, E, T1, S);
        false -> error({"wtf, internal type mismatch", T1, T2})
    end;
constr_expr(Env, Expr = {IdHead, _, _}, T, S)
  when IdHead =:= id orelse IdHead =:= qid ->
    case type_of(Env, Expr) of
        undefined ->
            Eq = ?op(nu(), '==', Expr),
            {{refined_t, ann(), T, [Eq]}, S};
        {_, {refined_t, Ann, B, _}} ->
            %% The missed predicate can be inferred from the equality
            Eq = ?op(nu(), '==', Expr),
            {{refined_t, Ann, B, [Eq]}
            , S
            };
        {_, T1} -> {T1, S}
    end;
constr_expr(_Env, I = {int, _, _}, T = ?int_tp, S) ->
    {?refined(T, [?op(nu(), '==', I)]), S};
constr_expr(_Env, {bool, _, B}, T, S) ->
    {?refined(T, [if B -> nu(); true -> ?op('!', nu()) end]), S};

constr_expr(Env, {tuple, Ann, Elems}, _, S0) ->
    {ElemsT, S1} = constr_expr_list(Env, Elems, S0),
    {{dep_tuple_t, Ann, ElemsT},
     S1
    };

constr_expr(Env, {record, Ann, FieldVals}, T, S0) ->
    {Fields, Vals} =
        lists:unzip([{Field, Val} || {field, _, [{proj, _, Field}], Val} <- FieldVals]),
    {ValsT, S1} = constr_expr_list(Env, Vals, S0),
    {{dep_record_t, Ann, T, lists:zip(Fields, ValsT)},
     S1
    };

constr_expr(_Env, Expr = {CmpOp, Ann}, {fun_t, _, _, [OpLT, OpRT], RetT = ?bool_tp}, S)
  when CmpOp =:= '<' orelse
       CmpOp =:= '=<' orelse
       CmpOp =:= '>' orelse
       CmpOp =:= '>=' orelse
       CmpOp =:= '==' orelse
       CmpOp =:= '!=' ->
    OpLV = fresh_id("opl"),
    OpRV = fresh_id("opr"),
    { {dep_fun_t, Ann, [],
       [{OpLV, ?refined(OpLT, [])}, {OpRV, ?refined(OpRT, [])}],
       ?refined(RetT, [?op(nu(), '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
      }
    , S
    };
constr_expr(_Env, Expr = {CmpOp, Ann}, {fun_t, _, _, [OpLT, OpRT], RetT = ?int_tp}, S)
  when CmpOp =:= '+' orelse
       CmpOp =:= '*' orelse
       CmpOp =:= '-' orelse
       CmpOp =:= '/' orelse
       CmpOp =:= 'mod' orelse
       CmpOp =:= '^' ->
    OpLV = fresh_id("opl"),
    OpRV = fresh_id("opr"),
    { {dep_fun_t, Ann, [],
       [ {OpLV, ?refined(OpLT, [])}
       , {OpRV, ?refined(OpRT, case CmpOp of
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
    { {dep_fun_t, Ann, [],
       [{N, ?refined(?int_t, [])}],
       ?refined(?int_t,
                [?op(nu(), '==', {app, [{format, prefix}|Ann], Expr, [N]})])
      }
    , S
    };
constr_expr(Env, {app, Ann, ?typed_p({id, _, "abort"}), _}, T, S0) ->
    ExprT = fresh_liquid(Env, T, "abort"),
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
    {ArgsT, S1} = constr_expr_list(Env, Args, S0),
    {_, {[], {variant_t, Constrs}}} = lookup_type(Env, Type),
    DepConstrs =
        [ {dep_constr_t, CAnn, Con,
           case lists:last(QName) == name(Con) of
               true  -> ArgsT;
               false -> [?refined(Arg, ?bool(true)) || Arg <- ConArgs]
           end
          }
          || {constr_t, CAnn, Con, ConArgs} <- Constrs
        ],
    {{dep_variant_t, Ann, Type, [{is_tag, Ann, nu(), QCon, ArgsT}], DepConstrs},
     S1
    };
constr_expr(Env, {app, Ann, F, Args}, _, S0) ->
    {{dep_fun_t, _, _, ArgsFT, RetT}, S1} = constr_expr(Env, F, S0),
    {ArgsT, S2} = constr_expr_list(Env, Args, S1),
    ArgSubst = [{X, Expr} || {{X, _}, Expr} <- lists:zip(ArgsFT, Args)],
    { apply_subst(ArgSubst, RetT)
    , [{subtype, [{context, {app, Ann, F, N}}|aeso_syntax:get_ann(ArgT)],
        Env, ArgT, ArgFT}
       || {{_, ArgFT}, ArgT, N} <- lists:zip3(ArgsFT, ArgsT, lists:seq(1, length(ArgsT)))
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
constr_expr(Env, {lam, Ann, Args, Body}, T = {fun_t, TAnn, _, _, RetT}, S0) ->
    ExternalExprT = fresh_liquid(Env, "lam", T),
    DepArgsT =
        [ {ArgId, fresh_liquid(Env, contravariant, "argl_" ++ ArgName, ArgT)}
         || {arg, _, ArgId = {id, _, ArgName}, ArgT} <- Args
        ],
    DepRetT = fresh_liquid(Env, "lam_ret", RetT),
    InternalExprT = {dep_fun_t, TAnn, [], DepArgsT, DepRetT},
    EnvBody = bind_vars(DepArgsT, Env),
    {BodyT, S1} = constr_expr(EnvBody, Body, S0),
    {ExternalExprT,
     [ {well_formed, Env, InternalExprT}
     , {well_formed, Env, ExternalExprT}
     , {subtype, Ann, Env, InternalExprT, ExternalExprT}
     , {subtype, aeso_syntax:get_ann(Body), EnvBody, BodyT, DepRetT}
     | S1
     ]
    };
constr_expr(Env, {proj, Ann, Rec, Field}, T, S0) ->
    ExprT = fresh_liquid(Env, "proj", T),
    {{dep_record_t, _, _, Fields}, S1} = constr_expr(Env, Rec, S0),
    [FieldT] =
        [ RecFieldT
         || {RecFieldName, RecFieldT} <- Fields,
            name(Field) == name(RecFieldName)
        ],
    {ExprT,
     [ {well_formed, Env, ExprT}
     , {subtype, Ann, Env, FieldT, ExprT}
     | S1
     ]
    };

constr_expr(Env, [E], _, S) ->
    constr_expr(Env, E, S);
constr_expr(Env0, [{letval, Ann, Pat, Val}|Rest], T, S0) ->
    ExprT = fresh_liquid(Env0, case Pat of
                             ?typed_p({id, _, Name}) -> Name;
                             _ -> "pat"
                         end, T), %% Required to have clean scoping
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
            [{typed, _,
              {app, _, {typed, _, {id, _, "require"}, _}, [Cond, _]},
              _}|Rest], T, S0) ->
    constr_expr(assert(Cond, Env), Rest, T, S0);
constr_expr(_Env, {string, _, _}, T, S0) ->
    {?refined(T), S0};
constr_expr(Env, [Expr|Rest], T, S0) ->
    {_, S1} = constr_expr(Env, Expr, S0),
    constr_expr(Env, Rest, T, S1);
constr_expr(_Env, [], T, S) ->
    {T, S};
constr_expr(_, E, A, B) ->
    error({todo, E, A, B}).

constr_cases(_Env, _Switched, _SwitchedT, _ExprT, Alts, S) ->
    constr_cases(_Env, _Switched, _SwitchedT, _ExprT, Alts, 0, S).
constr_cases(Env, Switched, _SwitchedT, _ExprT, [], _N, S) ->
    [{unreachable, aeso_syntax:get_ann(Switched), Env}|S];
constr_cases(Env, Switched, _SwitchedT, _ExprT, [], _N, S) ->
    [{reachable, aeso_syntax:get_ann(Switched), Env}|S];
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
    ?DBG("SWITCH PRED ~s", [aeso_pretty:pp(predicate, Pred)]),
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
match_to_pattern(Env, I = {int, _, _}, Expr, _Type, Pred) ->
    {Env, [?op(Expr, '==', I)|Pred]};
match_to_pattern(Env, {tuple, _, Pats}, Expr, {dep_tuple_t, _, Types}, Pred) ->
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
        [{Field, FieldT} || {{id, _, Field}, FieldT} <- FieldsT],
    lists:foldl(
      fun({field, _, [{proj, _, Field}], Pat}, {Env0, Pred0}) ->
              PatT = proplists:get_value(name(Field), FieldTypes),
              Ann = aeso_syntax:get_ann(Pat),
              Proj = {proj, Ann, Expr, qid(qname(Type) ++ [name(Field)])},
              {E, P} = match_to_pattern(Env0, Pat, Proj, PatT, Pred0),
              ?DBG("NEW PRED\n~s\n->\n~s", [aeso_pretty:pp(predicate, Pred), aeso_pretty:pp(predicate, P)]),
              {E, P}
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
     ).


group_subtypes(Cs) ->
    Subts = [C || C = {subtype, _, _, _, {refined_t, _, _, {template, _, _}}} <- Cs],
    Rest = Cs -- Subts,

    SubtsMap =
        lists:foldl(
          fun ({subtype, Ann, Env, T, {refined_t, _, Base, {template, Subst, LV}}}, Map) ->
                  maps:put(LV, {Base, [{Env, Ann, Subst, T}|element(2, maps:get(LV, Map, {{}, []}))]}, Map)
          end, #{}, Subts
         ),
    Rest ++ [ {subtype_group, Ts, Base, LV}
              || {LV, {Base, Ts}} <- maps:to_list(SubtsMap)
            ].


%% -- Substitution -------------------------------------------------------------

apply_subst1({id, _, X}, Expr, {id, _, X}) ->
    Expr;
apply_subst1({qid, _, X}, Expr, {qid, _, X}) ->
    Expr;
apply_subst1({tvar, _, X}, Expr, {tvar, _, X}) ->
    Expr;
apply_subst1({ltvar, X}, Expr, {ltvar, X}) ->
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

apply_subst(Subs, Q) when is_map(Subs) ->
    apply_subst(maps:to_list(Subs), Q);
apply_subst(Subs, Q) when is_list(Subs) ->
    lists:foldl(fun({X, Expr}, Q0) -> apply_subst1(X, Expr, Q0) end, Q, Subs).


%% -- Assignments --------------------------------------------------------------

cmp_qualifiers(Thing) ->
    %% [].
    [ ?op(nu(), '=<', Thing)
    , ?op(nu(), '>=', Thing)
    , ?op(nu(), '>', Thing)
    , ?op(nu(), '<', Thing)
    ].

eq_qualifiers(Thing) ->
    [ ?op(nu(), '==', Thing)
    , ?op(nu(), '!=', Thing)
    ].

int_qualifiers(Thing) ->
    cmp_qualifiers(Thing) ++ eq_qualifiers(Thing).

plus_int_qualifiers({int, _, 0}, _Thing) -> [];
plus_int_qualifiers(Int, Thing) ->
    int_qualifiers(?op(Thing, '+', Int)) ++ int_qualifiers(?op(Thing, '-', Int)).

var_int_qualifiers(Var) ->
    int_qualifiers(Var) ++ plus_int_qualifiers(?int(1), Var).

inst_pred_variant_tag(Type, Constrs) ->
    [ {is_tag, ann(), nu(), qid(lists:droplast(qname(Type)) ++ [name(Con)]), Args}
      || {constr_t, _, Con, Args} <- Constrs
    ].

inst_pred_int(Env) ->
    lists:concat(
      [ [Q || CoolInt <- Env#env.cool_ints,
              Q <- int_qualifiers(?int(CoolInt))
        ]
      , [ Q || {Var, {refined_t, _, ?int_tp, _}} <- maps:to_list(Env#env.var_env),
               Q <- var_int_qualifiers({id, ann(), Var})
        ]
      ]
     ).

inst_pred_bool(Env) ->
    lists:concat(
      [ [Q || CoolBool <- [true, false],
              Q <- eq_qualifiers(?bool(CoolBool))
        ]
      , [ Q || {Var, {refined_t, _, ?bool_tp, _}} <- maps:to_list(Env#env.var_env),
               Q <- eq_qualifiers({id, ann(), Var})
        ]
      ]
     ).

inst_pred_tvar(Env, TVar) ->
    [ Q || {Var, {refined_t, _, {tvar, _, TVar1}, _}} <- maps:to_list(Env#env.var_env),
           TVar == TVar1,
           Q <- eq_qualifiers({id, ann(), Var})
    ].

inst_pred(BaseT, Env) ->
    case BaseT of
        ?int_tp ->
            inst_pred_int(Env);
        ?bool_tp ->
            inst_pred_bool(Env);
        {qid, _, _} ->
            case lookup_type(Env, BaseT) of
                {_, {_, {variant_t, Constrs}}} ->
                    inst_pred_variant_tag(BaseT, Constrs);
                X -> error({todo, {inst_pred, X}})
            end;
        {tvar, _, TVar} ->
            inst_pred_tvar(Env, TVar);
        _ -> []
    end.

init_assg(Cs) ->
    lists:foldl(
      fun({well_formed, Env, {refined_t, _, BaseT, {template, _, LV}}}, Acc) ->
              AllQs = inst_pred(BaseT, Env),
              Acc#{LV => #ltinfo{base = BaseT, env = Env, predicate = AllQs}};
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
pred_of(Assg, {refined_t, _, _, P}) ->
    pred_of(Assg, P);
pred_of(Assg, Env = #env{path_pred = PathPred}) ->
    ScopePred = flatten_type_binds(Assg, fun(X) -> X end, type_binds(Env)),
    ScopePred ++ PathPred;
pred_of(_, _) ->
    [].

flatten_type_binds(Assg, Access, TB) ->
    [ Q
     || {Var, Type} <- TB,
        Q <- case Type of
                 {refined_t, _, _, P} ->
                     apply_subst1(nu(), Access(Var), pred_of(Assg, P));
                 {dep_tuple_t, _, Fields} ->
                     N = length(Fields),
                     flatten_type_binds(
                       Assg,
                       fun(X) -> {proj, ann(), Access(Var), X} end,
                       lists:zip(
                         [?tuple_proj_id(N, I) || I <- lists:seq(1, N)],
                         Fields
                        )
                      );
                 {dep_record_t, _, RT, Fields} ->
                     flatten_type_binds(
                       Assg,
                       fun(X) -> {proj, ann(), Access(Var), X} end,
                       [{qid(qname(RT) ++ [name(Field)]), T} || {Field, T} <- Fields]
                      );
                 {dep_variant_t, _, QType, Tag, Constrs} ->
                     TagPred = apply_subst1(nu(), Access(Var), pred_of(Assg, Tag)),
                     ConPred =
                         lists:flatten(
                           [ flatten_type_binds(
                               Assg,
                               fun(X) -> {proj, ann(), Access(Var), X} end,
                               lists:zip(
                                 [?adt_proj_id(qid(lists:droplast(qname(QType)) ++ [name(Con)]), I) || I <- lists:seq(1, length(Args))],
                                 Args
                              )
                              )
                             || {dep_constr_t, _, Con, Args} <- Constrs
                           ]),
                     TagPred ++ ConPred;
                 _ -> []
             end
    ].

simplify_assg(Assg) ->
    maps:map(fun(_K, V = #ltinfo{env = KEnv, base = BaseType, predicate = Qs}) ->
                     V#ltinfo{
                       predicate =
                           simplify_pred(
                             bind_var(nu(), BaseType, KEnv),
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
        { {dep_fun_t, _, _, ArgsSub, RetSub}
        , {dep_fun_t, _, _, ArgsSup, RetSup}
        } ->
            Contra =
                [ {subtype, Ann, Env0, ArgSupT, ArgSubT} %% contravariant!
                 || {{_, ArgSubT}, {_, ArgSupT}} <- lists:zip(ArgsSub, ArgsSup)
                ],
            Env1 =
                bind_vars([{Id, T} || {Id, T} <- ArgsSup], Env0),
            Subst =
                [{Id1, Id2} || {{Id1, _}, {Id2, _}} <- lists:zip(ArgsSub, ArgsSup)],
            split_constr([{subtype, Ann, Env1, apply_subst(Subst, RetSub), RetSup}|Contra]);
        {{dep_tuple_t, _, TSubs}, {dep_tuple_t, _, TSups}} ->
            split_constr([{subtype, Ann, Env0, TSub, TSup} ||
                             {TSub, TSup} <- lists:zip(TSubs, TSups)]);
        { {dep_record_t, _, _, FieldsSub}
        , {dep_record_t, _, _, FieldsSup}
        } ->
            FieldsSub1 = lists:keysort(1, FieldsSub),
            FieldsSup1 = lists:keysort(1, FieldsSup),
            split_constr(
              [ {subtype, Ann, Env0, FTSub, FTSup}
               || {{_, FTSub}, {_, FTSup}} <- lists:zip(FieldsSub1, FieldsSup1)
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
        _ -> [C]
    end;
split_constr1(C = {well_formed, Env0, T}) ->
    case T of
        {dep_fun_t, _, _, Args, Ret} ->
            FromArgs =
                [ {well_formed, Env0, ArgT}
                  || {_, ArgT} <- Args
                ],
            Env1 =
                bind_vars([{Id, ArgT} || {Id, ArgT} <- Args], Env0),
            split_constr([{well_formed, Env1, Ret}|FromArgs]);
        {dep_tuple_t, _, Ts} ->
            split_constr([{well_formed, Env0, Tt} || Tt <- Ts]);
        {dep_record_t, _, _, Fields} ->
            split_constr([{well_formed, Env0, TF} || {_, TF} <- Fields]);
        {dep_variant_t, _, Type, Tag, Constrs} ->
            split_constr(
              [ {well_formed, Env0, ?refined(Type, Tag)}
              | [ {well_formed, Env0, Arg}
                  || {dep_constr_t, _, _, Args} <- Constrs,
                     Arg <- Args
                ]
              ]
             );
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
        {well_formed, _, {refined_t, _, _, []}} ->
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

%% valid_in({well_formed, Env, {refined_t, _, Base, P}}, Assg) ->
%%     EnvPred = pred_of(Assg, Env), %% FIXME does this clause make sense?
%%     ConstrPred = pred_of(Assg, P),
%%     impl_holds(bind_nu(Base, Env), EnvPred, ConstrPred);
valid_in({well_formed, _, _}, _) ->
    true;
valid_in({subtype_group, Subs, Base, SupPredVar}, Assg) ->
    Ltinfo = assg_of(Assg, SupPredVar),
    lists:all(
      fun({Env, _, Subst, SubKVar}) ->
              VarPred = pred_of(Assg, SubKVar),
              ?DBG("COMPLEX SUBTYPE\n~s\n<:\n~p", [aeso_pretty:pp(predicate, VarPred), SupPredVar]),
              EnvPred = pred_of(Assg, Env),
              AssumpPred = EnvPred ++ VarPred,
              impl_holds(bind_var(nu(), Base, Env),
                         AssumpPred, apply_subst(Subst, Ltinfo#ltinfo.predicate))
      end,
      Subs
     );
valid_in({subtype, Ann, Env,
          {refined_t, _, _, SubP}, {refined_t, _, Base, SupP}}, Assg) when is_list(SupP) ->
    ?DBG("SIMPLE SUBTYPE\n~p\n<:\n~p", [SubP, SupP]),
    SubPred = pred_of(Assg, SubP),
    EnvPred = pred_of(Assg, Env),
    AssumpPred = EnvPred ++ SubPred,
    ConclPred = pred_of(Assg, SupP),
    case impl_holds(bind_var(nu(), Base, Env), AssumpPred, ConclPred) of
        true -> true;
        false ->
            ?DBG("**** CONTRADICTION"),
            throw({contradict, {Ann, SubPred, ConclPred}})
    end;
valid_in(C = {subtype, _, _, _, _}, _) -> %% We trust the typechecker
    ?DBG("SKIPPING SUBTYPE: ~s", [aeso_pretty:pp(constr, C)]),
    true;
valid_in(_, _) ->
    true.


weaken({subtype_group, Subs, Base, SubPredVar}, Assg) ->
    Ltinfo = assg_of(Assg, SubPredVar),
    Filtered =
        [ Q || Q <- Ltinfo#ltinfo.predicate,
               lists:all(fun({Env, _, Subst, Sub}) ->
                                 Valid = subtype_implies(
                                           bind_var(nu(), Base, Env),
                                           Sub, apply_subst(Subst, Q), Assg),
                                 Valid
                         end, Subs)
        ],
    NewLtinfo = Ltinfo#ltinfo{
                 predicate = Filtered
                },
    ?DBG("WEAKENED FROM\n~s\nTO\n~s", [aeso_pretty:pp(predicate, Ltinfo#ltinfo.predicate),
                                       aeso_pretty:pp(predicate, Filtered)
                                      ]),
    Assg#{SubPredVar => NewLtinfo};
weaken({well_formed, _Env, {refined_t, _, _, _}}, Assg) ->
    Assg.

subtype_implies(Env, {refined_t, _, _, Template}, Q, Assg) ->
    SubPred =
        case Template of
            {template, Subst, KVar} ->
                apply_subst(Subst, (assg_of(Assg, KVar))#ltinfo.predicate);
            P -> P
        end,
    EnvPred = pred_of(Assg, Env),
    AssumpPred = EnvPred ++ SubPred,
    impl_holds(Env, AssumpPred, Q);
subtype_implies(Env, {tvar, _, _}, Q, Assg) ->
    impl_holds(Env, pred_of(Assg, Env), Q).


check_reachable(Assg, [{reachable, Ann, Env}|Rest]) ->
    Pred = pred_of(Assg, Env),
    case impl_holds(Env, Pred, [?bool(false)]) of
        true -> throw({valid_unreachable, {Ann, Pred}});
        false -> check_reachable(Assg, Rest)
    end;
check_reachable(Assg, [{unreachable, Ann, Env}|Rest]) ->
    Pred = pred_of(Assg, Env),
    ?DBG("UNREACHABLE CHECK"),
    ?DBG("RAW ENV ~p", [Env]),
    ?DBG("PRED ENV ~s", [aeso_pretty:pp(predicate, Pred)]),
    case impl_holds(Env, Pred, [?bool(false)]) of
        true -> check_reachable(Assg, Rest);
        false -> throw({invalid_reachable, {Ann, Pred}})
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

declare_datatypes([]) ->
    ok;
declare_datatypes([{Name, {_Args, TDef}}|Rest]) ->
    TName = string:join(qname(Name), "."),
    case TDef of
        {alias_t, _} -> ok;
        {record_t, Fields} ->
            aeso_smt:send_z3_success(
              {app, "declare-datatypes",
               [{list, []}, %% TODO Args
                {list, [{app, TName,
                         [{app, "$mk_" ++ TName,
                           [{app, TName ++ "." ++ name(FName),
                             [type_to_smt(T)]}
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
               [{list, []}, %% TODO Args
                {list, [ {app, TName,
                          [ begin
                                QualCon = lists:droplast(qname(Name)) ++ [name(Con)],
                                ConName = string:join(QualCon, "."),
                                {app, ConName,
                                 [{app, name(?adt_proj_id(qid(QualCon), I)),
                                   [type_to_smt(T)]}
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


impl_holds(Env, Assump, Concl) when not is_list(Concl) ->
    impl_holds(Env, Assump, [Concl]);
impl_holds(Env, Assump, Concl) when not is_list(Assump) ->
    impl_holds(Env, [Assump], Concl);
impl_holds(_, _, []) -> true;
impl_holds(Env, Assump, Concl) ->
    ConclExpr  = {app, ann(), {'&&', ann()}, Concl}, %% Improper Sophia expr but who cares
    ?DBG("IMPL;\n* ASSUMPTION: ~s\n* CONCLUSION: ~s",
         [ string:join([aeso_pretty:pp(expr, E)|| E <- Assump], " && ")
         , string:join([aeso_pretty:pp(expr, E)|| E <- Concl],  " && ")
         ]),
    aeso_smt:scoped(
      fun() ->
              [ begin
                    aeso_smt:declare_const(expr_to_smt(Var), type_to_smt(T))
                end
                || {Var, T} <- type_binds(Env), element(1, T) =/= dep_fun_t,
                   is_smt_expr(Var),
                   is_smt_type(T)
              ],
              [ aeso_smt:assert(expr_to_smt(Expr))
                || Expr <- Assump
              ],
              aeso_smt:assert(expr_to_smt(?op('!', ConclExpr))),
              case aeso_smt:check_sat() of
                  {error, Err} -> throw({smt_error, Err});
                  Res ->
                      case Res of
                          true -> ?DBG("FALSE");
                          false  -> ?DBG("HOLDS")
                      end,
                      not Res
              end
      end).


is_smt_type(Expr) ->
    try type_to_smt(Expr) of
        _ -> true
    catch throw:{not_smt_type, _} ->
            false
    end.

type_to_smt({refined_t, _, T, _}) ->
    type_to_smt(T);
type_to_smt(?bool_tp) ->
    {var, "Bool"};
type_to_smt(?int_tp) ->
    {var, "Int"};
type_to_smt({tvar, _, _}) ->
    {var, "Int"}; % lol
type_to_smt({qid, _, QVar}) ->
    {var, string:join(QVar, ".")};
type_to_smt({dep_tuple_t, Ann, Ts}) ->
    type_to_smt({tuple_t, Ann, Ts});
type_to_smt(?tuple_tp(Types)) ->
    N = length(Types),
    {app, "$tuple" ++ integer_to_list(N),
     [type_to_smt(T) || T <- Types]
    };
type_to_smt({dep_record_t, _, T, _}) ->
    type_to_smt(T);
type_to_smt({dep_variant_t, _, T, _, _}) ->
    type_to_smt(T);
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
    {var, Var};
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
simplify_pred(Scope, Pred) ->
    ?DBG("*** SIMPLIFY PRED"),
    case impl_holds(Scope, Pred, [{bool, ann(), false}]) of
        true -> [{bool, ann(), false}];
        false -> simplify_pred(Scope, [], sort_preds_by_meaningfulness(Pred))
    end.
simplify_pred(_Scope, Prev, []) ->
    Prev;
simplify_pred(Scope, Prev, [Q|Post]) ->
    case impl_holds(Scope, Prev ++ Post, Q) of
        true ->
            simplify_pred(Scope, Prev, Post);
        false ->
            simplify_pred(Scope, [Q|Prev], Post)
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
a_normalize_to_simpl(Expr = {Op, _}, Type, Decls) when is_atom(Op) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {proj, _, _, _}, Type, Decls) ->
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
