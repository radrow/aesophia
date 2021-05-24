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
-define(d_nonzero_int, ?refined(?int_t, [?op(nu(), '!=', ?int(0))])).

-define(bool(B), {bool, ann(), B}).
-define(bool_tp, {id, _, "bool"}).
-define(bool_t, {id, ann(), "bool"}).

-define(string(S), {string, _, S}).
-define(string_tp, {id, _, "string"}).
-define(string_t, {id, ann(), "string"}).

-define(typed(Expr, Type), {typed, element(2, Expr), Expr, Type}).
-define(typed_p(Expr), {typed, _, Expr, _}).
-define(typed_p(Expr, Type), {typed, _, Expr, Type}).


%% -- Types --------------------------------------------------------------------

%% Type imports
-type predicate()   :: aeso_syntax:predicate().
-type expr()        :: aeso_syntax:expr().
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

-record(scope, {fun_env = #{} :: fun_env()}).
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
-type variance() :: contravariant | covariant | forced_covariant.

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
bind_var(Id, T, Env) ->
    case is_smt_type(T) of
        true -> Env#env{ var_env = (Env#env.var_env)#{name(Id) => T}};
        false -> Env
    end.

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

%% Lookup in env. Currently only types of vars/funs. TODO: types
-spec lookup_env(env(), term, qname()) -> false | {qname(), lutype()}.
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

-spec lookup_env1(env(), term, qname()) -> false | {qname(), lutype()}.
lookup_env1(#env{ scopes = Scopes }, Kind, QName) ->
    Qual = lists:droplast(QName),
    Name = lists:last(QName),
    case maps:get(Qual, Scopes, false) of
        false -> false;
        #scope{ fun_env = Funs } ->
            Defs = case Kind of
                     term -> Funs
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
find_cool_ints([H|T], Acc0) ->
    Acc1 = find_cool_ints(H, Acc0),
    find_cool_ints(T, Acc1);
find_cool_ints(T, Acc) when is_tuple(T) ->
    find_cool_ints(tuple_to_list(T), Acc);
find_cool_ints(_, Acc) ->
    Acc.

with_cool_ints_from(AST, Env = #env{cool_ints = CI}) ->
    Env#env{cool_ints = find_cool_ints(AST) ++ CI}.

-spec bind_ast_funs(ast(), env()) -> env().
bind_ast_funs(AST, Env) ->
    lists:foldr(
      fun({HEAD, _, Con, Defs}, Env0)
            when HEAD =:= namespace orelse HEAD =:= contract orelse HEAD =:= contract_main ->
              Env1 = push_scope(Con, Env0),
              Env2 = bind_funs(
                       [ begin
                             ArgsT =
                                 [ {ArgName, fresh_liquid(contravariant, "arg_" ++ StrName, T)}
                                   || ?typed_p(ArgName = {id, _, StrName}, T) <- Args
                                 ],
                             TypeDep = {dep_fun_t, FAnn, [], ArgsT, fresh_liquid("ret", RetT)},
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
fresh_template(forced_covariant, Name) -> {template, [], fresh_ltvar(Name)};
fresh_template(contravariant, _) -> [].

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
-spec fresh_liquid(name(), term()) -> term().
fresh_liquid(Hint, Type) ->
    fresh_liquid(covariant, Hint, Type).
-spec fresh_liquid(name(), variance(), term()) -> term().
fresh_liquid(Variance, Hint, Type = {id, Ann, _}) ->
    {refined_t, Ann, Type, fresh_template(Variance, Hint)};
fresh_liquid(Variance, Hint, {fun_t, Ann, Named, Args, Ret}) ->
    { dep_fun_t, Ann, Named
    , [{fresh_id("arg"),
        fresh_liquid(switch_variance(Variance), Hint ++ "_argl", Arg)}
       || Arg <- Args]
    , fresh_liquid(Variance, Hint, Ret)
    };
fresh_liquid(_, _, []) -> [];
fresh_liquid(Variance, Hint, [H|T]) ->
    [fresh_liquid(Variance, Hint, H)|fresh_liquid(Variance, Hint, T)];
fresh_liquid(Variance, Hint, T) when is_tuple(T) ->
    list_to_tuple(fresh_liquid(Variance, Hint, tuple_to_list(T)));
fresh_liquid(_, _, X) -> X.

-spec switch_variance(variance()) -> variance().
switch_variance(covariant) ->
    contravariant;
switch_variance(contravariant) ->
    covariant;
switch_variance(forced_covariant) ->
    forced_covariant.


%% -- Entrypoint ---------------------------------------------------------------

refine_ast(AST) ->
    Env0 = init_env(),
    Env1 = with_cool_ints_from(AST, Env0),
    Env2 = bind_ast_funs(AST, Env1),
    {AST1, CS0} = constr_ast(Env2, AST),
    CS1 = simplify(CS0),
    CS2 = group_subtypes(CS1),
    try solve(Env2, CS2) of
        Assg ->
            AST2 = apply_assg(Assg, AST1),
            {ok, AST2}
    catch throw:E ->
            {error, E}
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
constr_con(Env0, {contract, Ann, Con, Defs}, S0) ->
    Env1 = push_scope(Con, Env0),
    {Defs1, S1} =
        lists:foldr(
          fun(Def, {Decls, S00}) ->
                  {Decl, S01} = constr_letfun(Env1, Def, S00),
                  {[Decl|Decls], S01}
          end,
          {[], S0}, Defs
         ),
    {{contract, Ann, Con, Defs1}, S1};
constr_con(Env0, {namespace, Ann, Con, Defs}, S0) ->
    Env1 = push_scope(Con, Env0),
    {Defs1, S1} =
        lists:foldr(
          fun(Def, {Decls, S00}) ->
                  {Decl, S01} = constr_letfun(Env1, Def, S00),
                  {[Decl|Decls], S01}
          end,
          {[], S0}, Defs
         ),
    {{namespace, Ann, Con, Defs1}, S1}.

-spec constr_letfun(env(), letfun(), [constr()]) -> {fundecl(), [constr()]}.
constr_letfun(Env0, {letfun, Ann, Id = {id, _, Name}, Args, RetT, Body}, S0) ->
    ArgsT =
        [ {ArgId, fresh_liquid(contravariant, "argi_" ++ ArgName, T)}
          || ?typed_p(ArgId = {id, _, ArgName}, T) <- Args
        ],
    S1 = [ {well_formed, Env0, T} || {_, T} <- ArgsT ] ++ S0,
    Env1 = bind_vars(ArgsT, Env0),
    Body1 = a_normalize(Body),
    ?DBG("NORMALIZED:\n~s\n\nTO\n\n~s\n\n\n", [aeso_pretty:pp(expr, Body), aeso_pretty:pp(expr, Body1)]),
    DepRetT = fresh_liquid("ret_" ++ Name, RetT),
    {BodyT, S2} = constr_expr(Env1, Body1, S1),
    DepSelfT =
        { dep_fun_t, Ann, []
        , ArgsT
        , DepRetT
        },
    {_, GlobalFunType} = type_of(Env1, Id),
    S3 = [ {subtype, Ann, Env1, DepSelfT, GlobalFunType}
         , {subtype, Ann, Env1, BodyT, DepRetT}
         , {well_formed, Env1, GlobalFunType}
         , {well_formed, Env1, DepRetT}
         | S2
         ],

    {{fun_decl, Ann, Id, DepSelfT}, S3}.


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
        {_, {refined_t, Ann, B, P}} ->
            Eq = ?op(nu(), '==', Expr), %% IF THIS IS THE ONLY Q THEN IT WORKS BETTER
            {{refined_t, Ann, B, [Eq]}
            %% { {refined_t, Ann, B, P}
            %% , [{subtype, Env, {refined_t, Ann, B, [Eq]}, T1}|S] %% FIXME Flip?
            , S
            };
        {_, T1} -> {T1, S}
    end;
constr_expr(_Env, I = {int, _, _}, T = ?int_tp, S) ->
    {?refined(T, [?op(nu(), '==', I)]), S};
constr_expr(_Env, {bool, _, B}, T, S) ->
    {?refined(T, [if B -> nu(); true -> ?op('!', nu()) end]), S};

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
       ], ?refined(RetT, [ ?op(nu(), '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
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
    {?refined(T), [{unreachable, Ann, Env}|S0]};
constr_expr(Env, {app, Ann, F, Args}, _, S0) ->
    {{dep_fun_t, _, _, ArgsFT, RetT}, S1} = constr_expr(Env, F, S0),
    {ArgsT, S2} = constr_expr_list(Env, Args, S1),
    ArgSubst = [{X, Expr} || {{X, _}, Expr} <- lists:zip(ArgsFT, Args)],
    { apply_subst(ArgSubst, RetT)
    , [{subtype, [{context, {app, Ann, F, N}}|aeso_syntax:get_ann(ArgT)],
        Env, ArgT, ArgFT} || {{_, ArgFT}, ArgT, N} <- lists:zip3(ArgsFT, ArgsT, lists:seq(1, length(ArgsT)))] ++
      S2
    };
constr_expr(Env, {'if', _, Cond, Then, Else}, T, S0) ->
    ExprT = fresh_liquid("if", T),
    {_, S1} = constr_expr(Env, Cond, S0),
    {ThenT, S2} = constr_expr(assert(Cond, Env), Then, S1),
    {ElseT, S3} = constr_expr(assert(?op('!', Cond), Env),Else, S2),
    { ExprT
    , [ {well_formed, Env, ExprT}
      , {subtype, [{context, then}|aeso_syntax:get_ann(Then)], assert(Cond, Env), ThenT, ExprT}
      , {subtype, [{context, else}|aeso_syntax:get_ann(Else)], assert(?op('!', Cond), Env), ElseT, ExprT}
      | S3
      ]
    };
constr_expr(Env, {switch, _, Switched, Alts}, T, S0) ->
    ExprT = fresh_liquid("switch_bool", T),
    {SwitchedT, S1} = constr_expr(Env, Switched, S0),
    S2 = constr_cases(Env, Switched, SwitchedT, ExprT, Alts, S1),
    {ExprT
    , [{well_formed, Env, ExprT}|S2]
    };
constr_expr(Env, {lam, Ann, Args, Body}, {fun_t, TAnn, _, _, RetT}, S0) ->
    DepArgsT =
        [ {ArgId, fresh_liquid(contravariant, "argl_" ++ ArgName, ArgT)}
         || {arg, _, ArgId = {id, _, ArgName}, ArgT} <- Args
        ],
    DepRetT = fresh_liquid("lam_ret", RetT),
    ExprT = {dep_fun_t, TAnn, [], DepArgsT, DepRetT},
    EnvBody = bind_vars(DepArgsT, Env),
    {BodyT, S1} = constr_expr(EnvBody, Body, S0),
    {ExprT,
     [ {well_formed, Env, ExprT}
     , {subtype, Ann, EnvBody, BodyT, DepRetT}
     | S1
     ]
    };
constr_expr(Env, [E], _, S) ->
    constr_expr(Env, E, S);
constr_expr(Env0, [{letval, Ann, Pat, Val}|Rest], T, S0) ->
    ExprT = fresh_liquid(case Pat of
                             {typed, _, {id, _, Name}, _} -> Name;
                             _ -> "pat"
                         end, T), %% Required to have clean scoping
    {ValT, S1} = constr_expr(Env0, Val, S0),
    {Env1, _} = match_to_pattern(Env0, Pat, Val, ValT),
    {RestT, S2} = constr_expr(Env1, Rest, T, S1),
    {ExprT,
     [ {well_formed, Env0, ExprT}
     , {subtype, Ann, Env1, RestT, ExprT}
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
    {EnvCase, Pred} = match_to_pattern(Env0, Pat, Switched, SwitchedT),
    ?DBG("NEW PRED ~s", [aeso_pretty:pp(predicate, Pred)]),
    Env1 = case Pred of
               [] -> assert(?bool(false), Env0);
               [H|T] ->
                   PredExpr = lists:foldl(
                                fun(E, Acc) -> ?op(E, '&&', Acc)
                                end, H, T
                               ),
                   assert(?op('!',  PredExpr), Env0)
           end,
    {CaseDT, S1} = constr_expr(EnvCase, Case, S0),
    constr_cases(Env1, Switched, SwitchedT, ExprT, Rest,
                 [ {subtype, [{context, {switch, N}}|Ann], EnvCase, CaseDT, ExprT}
                 , {reachable, Ann, EnvCase}
                 | S1
                 ]
                ).

%% match_to_pattern computes
%%   - Env which will bind variables
%%   - Predicate to assert that match holds
match_to_pattern(Env, Pat, Expr, Type) ->
    {Env1, Pred} = match_to_pattern(Env, Pat, Expr, Type, []),
    {assert(Pred, Env1), Pred}.
match_to_pattern(Env, {typed, _, Pat, _}, Expr, Type, Pred) ->
    match_to_pattern(Env, Pat, Expr, Type, Pred);
match_to_pattern(Env, {id, _, "_"}, _Expr, _Type, Pred) ->
    {Env, Pred};
match_to_pattern(Env, Id = {id, _, _}, _Expr, Type, Pred) ->
    {bind_var(Id, Type, Env), Pred};
match_to_pattern(Env, I = {int, _, _}, Expr, _Type, Pred) ->
    {Env, [?op(Expr, '==', I)|Pred]}.


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
    int_qualifiers({id, ann(), Var}) ++ plus_int_qualifiers(?int(1), {id, ann(), Var}).

inst_pred_int(Env) ->
    lists:concat(
      [ [Q || CoolInt <- Env#env.cool_ints,
              Q <- int_qualifiers(?int(CoolInt))]
      , [ Q || {Var, {refined_t, _, ?int_tp, _}} <- maps:to_list(Env#env.var_env),
               Q <- var_int_qualifiers(Var)
        ]
      ]
     ).

inst_pred(BaseT, Env) ->
    case BaseT of
        ?int_tp ->
            inst_pred_int(Env);
        _ -> []
    end.

init_assg(Cs) ->
    lists:foldl(
      fun({well_formed, Env, {refined_t, _, BaseT, {template, _, LV}}}, Acc) ->
              AllQs = inst_pred(BaseT, Env),
              ?DBG("INIT ASSG OF ~p:\n~s", [LV, aeso_pretty:pp(predicate, AllQs)]),
              Acc#{LV => #ltinfo{base = BaseT, env = Env, predicate = AllQs}};
         (_, Acc) -> Acc
      end, #{}, Cs).

assg_of(Assg, Var = {ltvar, _}) ->
    case maps:get(Var, Assg, undef) of
        undef -> error({undef_assg, Var});
            %% #ltinfo
            %%     { base = {id, ann(), "int"} %% FIXME NOT ONLY INT
            %%     , predicate = []
            %%     , env = init_env()
            %%     };
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
    ScopePred =
        [ Qual
         || {Var, {refined_t, _, _, VarPred}} <- type_binds(Env),
            Qual <- apply_subst1(nu(), Var, pred_of(Assg, VarPred))
        ],
    ScopePred ++ PathPred;
pred_of(_, _) ->
    [].

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

simplify(L) when is_list(L) ->
    simplify(L, []).
simplify([H|T], Acc) ->
    HC = simplify1(H),
    simplify(T, HC ++ Acc);
simplify([], Acc) ->
    filter_obvious(Acc).

simplify1(C = {subtype, Ann, Env0, SubT, SupT}) ->
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
            simplify([{subtype, Ann, Env1, RetSub, RetSup}|Contra]);
        _ -> [C]
    end;
simplify1(C = {well_formed, Env0, T}) ->
    case T of
        {dep_fun_t, _, _, Args, Ret} ->
            FromArgs =
                [ {well_formed, Env0, ArgT}
                  || {_, ArgT} <- Args
                ],
            Env1 =
                bind_vars([{Id, ArgT} || {Id, ArgT} <- Args], Env0),
            simplify([{well_formed, Env1, Ret}|FromArgs]);
        _ -> [C]
    end;
simplify1(C = {reachable, _, _}) ->
    [C];
simplify1(C = {unreachable, _, _}) ->
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

solve(_Env, Cs) ->
    ?DBG("CONSTRAINTS:\n~s", [string:join([aeso_pretty:pp(constr, C)||C <- Cs], "\n\n")]),
    Assg0 = solve(init_assg(Cs), Cs, Cs),
    check_reachable(Assg0, Cs),
    simplify_assg(Assg0).
solve(Assg, _, []) ->
    Assg;
solve(Assg, AllCs, [C|Rest]) ->
    ?DBG("SOLVING:\n~s", [aeso_pretty:pp(constr, C)]),
    case C of
        {subtype_group, _, _, R = {ltvar, _}} ->
            ?DBG("ASSG OF ~p: ~s", [R, aeso_pretty:pp(predicate, (assg_of(Assg, R))#ltinfo.predicate)]);
        _ -> ok
    end,
    case valid_in(C, Assg) of
        false -> ?DBG("CONSTR INVALID"),
                 Weakened = weaken(C, Assg),
                 solve(Weakened, AllCs, AllCs);
        true  -> ?DBG("CONSTR VALID"), solve(Assg, AllCs, Rest)
    end.

%% valid_in({well_formed, Env, {refined_t, _, Base, P}}, Assg) ->
%%     EnvPred = pred_of(Assg, Env), %% FIXME does this clause make sense?
%%     ConstrPred = pred_of(Assg, P),
%%     impl_holds(bind_nu(Base, Env), EnvPred, ConstrPred);
valid_in({well_formed, _, _}, _) ->
    true;
valid_in({subtype_group, Subs, Base, SupPredVar} = C, Assg) ->
    Ltinfo = assg_of(Assg, SupPredVar),
    ?DBG("CHECKING VALID FOR COMP SUB\n~s", [aeso_pretty:pp(constr, C)]),
    lists:all(
      fun({Env, _, Subst, SubKVar}) ->
              VarPred = pred_of(Assg, SubKVar),
              EnvPred = pred_of(Assg, Env),
              AssumpPred = EnvPred ++ VarPred,
              impl_holds(bind_var(nu(), Base, Env),
                         AssumpPred, apply_subst(Subst, Ltinfo#ltinfo.predicate))
      end,
      Subs
     );
valid_in({subtype, Ann, Env,
          {refined_t, _, _, SubP}, {refined_t, _, Base, SupP}} = C, Assg) when is_list(SupP) ->
    ?DBG("CHECKING VALID FOR RIGID SIMP SUB\n~s", [aeso_pretty:pp(constr, C)]),
    SubPred = pred_of(Assg, SubP),
    EnvPred = pred_of(Assg, Env),
    AssumpPred = EnvPred ++ SubPred,
    ConclPred = pred_of(Assg, SupP),
    case impl_holds(bind_var(nu(), Base, Env), AssumpPred, ConclPred) of
        true -> true;
        false ->
            ?DBG("**** CONTRADICTION"),
            throw({contradict, Ann, SubPred, ConclPred})
    end;
valid_in(C = {subtype, _, _, _, _}, _) -> %% We trust the typechecker
    ?DBG("SKIPPING SUBTYPE: ~s", [aeso_pretty:pp(constr, C)]),
    true;
valid_in(_, _) ->
    true.


weaken({subtype_group, Subs, Base, SubPredVar}, Assg) ->
    ?DBG("**** WEAKENING SUB FOR ~p", [SubPredVar]),
    Ltinfo = assg_of(Assg, SubPredVar),
    Filtered =
        [ Q || Q <- Ltinfo#ltinfo.predicate,
               lists:all(fun({Env, _, Subst, Sub}) ->
                                 Valid = subtype_implies(
                                           bind_var(nu(), Base, Env),
                                           Sub, apply_subst(Subst, Q), Assg),
                                 case Valid of
                                     true -> ?DBG("SUB VALID");
                                     false -> ?DBG("SUB INVALID")
                                 end,
                                 Valid
                         end, Subs)
        ],
    ?DBG("**** WEAKENED\n* FROM ~s\n* TO ~s",
         [aeso_pretty:pp(predicate, Ltinfo#ltinfo.predicate), aeso_pretty:pp(predicate, Filtered)]),
    NewLtinfo = Ltinfo#ltinfo{
                 predicate = Filtered
                },
    Assg#{SubPredVar => NewLtinfo};
weaken({well_formed, Env, {refined_t, _, _, P}}, Assg) ->
    Assg. %% TODO

subtype_implies(Env, {refined_t, _, _, Template}, Q, Assg) ->
    SubPred =
        case Template of
            {template, Subst, KVar} ->
                apply_subst(Subst, (assg_of(Assg, KVar))#ltinfo.predicate);
            P -> P
        end,
    EnvPred = pred_of(Assg, Env),
    AssumpPred = EnvPred ++ SubPred,
    ?DBG("APRED ~p", [AssumpPred]),
    impl_holds(Env, AssumpPred, Q).

check_reachable(Assg, [{reachable, Ann, Env}|Rest]) ->
    Pred = pred_of(Assg, Env),
    case impl_holds(Env, Pred, [?bool(false)]) of
        true -> throw({valid_unreachable, Ann, Env#env.path_pred});
        false -> check_reachable(Assg, Rest)
    end;
check_reachable(Assg, [{unreachable, Ann, Env}|Rest]) ->
    Pred = pred_of(Assg, Env),
    case impl_holds(Env, Pred, [?bool(false)]) of
        true -> check_reachable(Assg, Rest);
        false -> throw({invalid_reachable, Ann, Env#env.path_pred})
    end;
check_reachable(Assg, [_|Rest]) ->
    check_reachable(Assg, Rest);
check_reachable(_, []) ->
    ok.


%% -- SMT Solving --------------------------------------------------------------

impl_holds(Env, Assump, Concl) when not is_list(Concl) ->
    impl_holds(Env, Assump, [Concl]);
impl_holds(Env, Assump, Concl) when not is_list(Assump) ->
    impl_holds(Env, [Assump], Concl);
impl_holds(_, _, []) -> true;
impl_holds(Env, Assump, Concl) ->
    ConclExpr  = {app, ann(), {'&&', ann()}, Concl}, %% Improper sophia expr but who cares
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
type_to_smt(T) ->
    throw({not_smt_type, T}).

is_smt_expr(Expr) ->
    try expr_to_smt(Expr) of
        _ -> true
    catch throw:{not_smt_expr, _} ->
            false
    end.

expr_to_smt({id, _, Var}) ->
    {var, Var};
expr_to_smt({qid, _, QVar}) ->
    {var, string:join(QVar, ".")};
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
expr_to_smt({'!=', _}) -> "distinct";
expr_to_smt({'<', _})  -> "<";
expr_to_smt({'>', _})  -> ">";
expr_to_smt({'+', _})  -> "+";
expr_to_smt({'-', _})  -> "-";
expr_to_smt({'*', _})  -> "*";
expr_to_smt({'/', _})  -> "div";
expr_to_smt({'!', _})  -> "not";
expr_to_smt({'^', _})  -> "^";
expr_to_smt({'mod', _})  -> "mod";
expr_to_smt(E) -> throw({not_smt_expr, E}).


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
                  ValueL = proplists:get_value(OpL, OpList, 0) + SimplBonus(LL) + SimplBonus(LR),
                  ValueR = proplists:get_value(OpR, OpList, 0) + SimplBonus(RL) + SimplBonus(RR),
                  ValueL =< ValueR;
              (_, _) -> true
          end,
    lists:sort(Cmp, Preds1).

%% this is absolutely heuristic
simplify_pred(Scope, Pred) ->
    ?DBG("***** SIMPLIFY"),
    simplify_pred(Scope, [], sort_preds_by_meaningfulness(Pred)).
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
