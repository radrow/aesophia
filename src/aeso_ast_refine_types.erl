-module(aeso_ast_refine_types).
-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").
-define(DBG(A, B), ?debugFmt(A, B)).
-define(DBG(A), ?debugMsg(A)).

%% -- Types --------------------------------------------------------------------

%% Type imports
-type predicate()   :: aeso_syntax:predicate().
-type expr()        :: aeso_syntax:expr().
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
        , interesting_ints = []                :: [integer()]
        , namespace        = []                :: qname()
        }).
-type env() :: #env{}.

%% Grouped subtype constraint
-type subtype_constr() :: {subtype, [{env(), subst(), lutype()}], ltvar()}.

%% Constraint
-type constr() :: {subtype, env(), lutype(), lutype()}
                | subtype_constr()
                | {well_formed, env(), lutype()}.

%% Information about ltvar
-record(ltinfo, {base :: aeso_syntax:type(), curr_qs :: predicate(), env :: env()}).
-type ltinfo() :: #ltinfo{}.

%% Position in type
-type variance() :: contravariant | covariant.

-spec ann() -> ann().
ann() -> [{origin, hagia}].
-spec ann(ann()) -> ann().
ann(L) -> [{origin, hagia}|L].

%% -- Name manipulation --------------------------------------------------------

-spec name(aeso_syntax:id() | aeso_syntax:con()) -> name().
name({_, _, X}) -> X.

-spec qname(type_id()) -> qname().
qname({id,   _, X})  -> [X];
qname({qid,  _, Xs}) -> Xs;
qname({con,  _, X})  -> [X];
qname({qcon, _, Xs}) -> Xs.

-spec qid(ann(), qname()) -> aeso_syntax:id() | aeso_syntax:qid().
qid(Ann, [X]) -> {id, Ann, X};
qid(Ann, Xs)  -> {qid, Ann, Xs}.

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
    Name = name(Con),
    New  = Env#env.namespace ++ [Name],
    Env#env{ namespace = New, scopes = (Env#env.scopes)#{ New => #scope{} } }.

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
bind_var({id, _, X}, T, Env) ->
    Env#env{ var_env = (Env#env.var_env)#{X => T}}.

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
            [X] when Kind == term -> proplists:get_value(X, Env#env.var_env, false);
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
            case proplists:get_value(Name, Defs, false) of
                false -> false;
                E -> {QName, E}
            end
    end.

-spec type_of(env(), type_id()) -> lutype().
type_of(Env, Id) ->
    case lookup_env(Env, term, qname(Id)) of
        false ->
            error({unbound_variable, Id});
        {QId, Ty} -> {set_qname(QId, Id), Ty}
    end.


%% -- Initialization -----------------------------------------------------------

-spec init_refiner() -> ok.
init_refiner() ->
    put(ltvar_supply, 0),
    put(id_supply, 0),
    ok.

%% -- Fresh stuff --------------------------------------------------------------

-spec fresh_ltvar(name()) -> ltvar().
fresh_ltvar(Name) ->
    I = get(ltvar_supply),
    put(ltvar_supply, I + 1),
    {ltvar, Name ++ "_" ++ integer_to_list(I)}.

-spec fresh_template(name()) -> lutype().
fresh_template(Name) -> fresh_template(covariant, Name).
fresh_template(covariant, Name) -> {template, [], fresh_ltvar(Name)};
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
    {typed, ann(), fresh_id(Name), Type}.


%% -- Constraint generation ----------------------------------------------------

-spec switch_variance(variance()) -> variance().
switch_variance(covariant) ->
    contravariant;
switch_variance(contravariant) ->
    covariant.

%% Decorates base types with templates through the AST
-spec decorate_base_types(name(), term()) -> term().
decorate_base_types(Hint, Type) ->
    decorate_base_types(covariant, Hint, Type).
-spec decorate_base_types(name(), variance(), term()) -> term().
decorate_base_types(Variance, Hint, Type = {id, Ann, "int"}) ->
    {refined_t, Ann, Type, fresh_template(Variance, Hint)};
decorate_base_types(Variance, Hint, Type = {id, Ann, "bool"}) ->
    {refined_t, Ann, Type, fresh_template(Variance, Hint)};
decorate_base_types(Variance, Hint, {fun_t, Ann, Named, Args, Ret}) ->
    { dep_fun_t, Ann, Named
    , [{fresh_id("arg"),
        decorate_base_types(switch_variance(Variance), Hint ++ "_argl", Arg)}
       || Arg <- Args]
    , decorate_base_types(Variance, Hint, Ret)
    };
decorate_base_types(_, _, []) -> [];
decorate_base_types(Variance, Hint, [H|T]) ->
    [decorate_base_types(Variance, Hint, H)|decorate_base_types(Variance, Hint, T)];
decorate_base_types(Variance, Hint, T) when is_tuple(T) ->
    list_to_tuple(decorate_base_types(Variance, Hint, tuple_to_list(T)));
decorate_base_types(_, _, X) -> X.

-spec constr_con(env(), aeso_syntax:decl()) -> {env(), aeso_syntax:decl(), [constr()]}.
constr_con(Env0, {contract, Ann, Con, Defs}) ->
    Env1 = push_scope(Con, Env0),
    Env2 =
        bind_funs(
          [ begin
                ArgsT =
                    [ {ArgName, decorate_base_types(contravariant, "arg_" ++ StrName, T)}
                      || {typed, _, ArgName = {id, _, StrName}, T} <- Args
                    ],
                TypeDep = {dep_fun_t, FAnn, [], ArgsT, decorate_base_types("ret", RetT)},
                {Name, TypeDep}
            end
           || {letfun, FAnn, {id, _, Name}, Args, RetT, _} <- Defs
          ],
          Env1),
    {Defs1, Ss} = lists:unzip(
                   [constr_letfun(Env2, Def, []) || Def <- Defs]
                  ),
    S = lists:flatten(Ss),
    {Env2, {contract, Ann, Con, Defs1}, S}.

-spec constr_letfun(env(), aeso_syntax:letfun(), [constr()]) -> {aeso_syntax:fundecl(), [constr()]}.
constr_letfun(Env0, {letfun, Ann, Id = {id, _, Name}, Args, _RetT, Body}, S) ->
    ArgsT =
        [ {ArgName, decorate_base_types(contravariant, "argi_" ++ StrName, T)}
          || {typed, _, ArgName = {id, _, StrName}, T} <- Args
        ],
    Env1 = bind_vars(ArgsT, Env0),
    Body1 = a_normalize(Body),
    ?DBG("NORMALIZED:\n~s\n\nTO\n\n~s\n\n\n", [aeso_pretty:pp(expr, Body), aeso_pretty:pp(expr, Body1)]),
    {DepRetT, S1} = constr_expr(Env1, Body1, S),
    DepSelfT =
        { dep_fun_t, Ann, []
        , ArgsT
        , DepRetT
        },
    GlobalFunType = maps:get(Name, Env0#env.type_binds),
    S2 = [ {subtype, Env1, DepSelfT, GlobalFunType}
         , {well_formed, Env1, GlobalFunType}
         | S1
         ],

    {{fun_decl, Ann, Id, DepSelfT}, S2}.

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
-define(int(I), {int, ann(), I}).
-define(int_tp, {id, _, "int"}).
-define(bool_tp, {id, _, "bool"}).
-define(typed(Expr, Type), {typed, element(2, Expr), Expr, Type}).

constr_expr(Env, {typed, Ann, {app, Ann1, F, Args}, RetT}, S)
  when element(1, F) =/= typed ->
    ArgTypes = [ArgT || {typed, _, _, ArgT} <- Args],
    TypedF = {typed, Ann, F, {fun_t, Ann, ann(), ArgTypes, RetT}},
    constr_expr(Env, {typed, Ann, {app, Ann1, TypedF, Args}, RetT}, S);
constr_expr(Env, {typed, _, Expr, T}, S) ->
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
constr_expr(Env, Expr = {id, _, Name}, T, S) ->
    case get_var(Env, Name) of
        undefined ->
            Eq = ?op(nu, '==', Expr),
            {{refined_t, ann(), T, [Eq]}, S};
        {refined_t, Ann, B, P} = T1 ->
            Eq = ?op(nu, '==', Expr), %% IF THIS IS THE ONLY Q THEN IT WORKS BETTER
            { {refined_t, Ann, B, P}
            %% , [{subtype, Env, {refined_t, Ann, B, [Eq]}, T1}|S] %% FIXME Flip?
            , S
            };
        T1 -> {T1, S}
    end;
constr_expr(Env, {qid, Ann, Qid}, T, S) ->
    constr_expr(Env, {id, Ann, lists:last(Qid)}, T, S); %% FIXME
constr_expr(_Env, I = {int, _, _}, T = ?int_tp, S) ->
    {?refined(T, [?op(nu, '==', I)]), S};
constr_expr(_Env, {bool, _, B}, T, S) ->
    {?refined(T, [if B -> nu; true -> ?op('!', nu) end]), S};

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
       ?refined(RetT, [?op(nu, '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
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
                                   'mod' -> [?op(nu, '>',  ?int(0))];
                                   '/'   -> [?op(nu, '!=', ?int(0))];
                                   '^'   -> [?op(nu, '>=', ?int(0))];
                                   _     -> []
                               end)}
       ], ?refined(RetT, [ ?op(nu, '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
      }
    , S
    };
constr_expr(_Env, Expr = {'-', Ann}, _, S) ->
    N = fresh_id("n"),
    { {dep_fun_t, Ann, [],
       [{N, ?refined({id, ann(), "int"}, [])}],
       ?refined({id, ann(), "int"},
                [?op(nu, '==', {app, [{format, prefix}|Ann], Expr, [N]})])
      }
    , S
    };
constr_expr(Env, {app, _, F, Args}, _, S0) ->
    {ExprT = {dep_fun_t, _, _, ArgsFT, RetT}, S1} = constr_expr(Env, F, S0),
    {ArgsT, S2} = constr_exprs(Env, Args, S1),
    ArgSubst = [{X, Expr} || {{X, _}, Expr} <- lists:zip(ArgsFT, Args)],
    { apply_subst(ArgSubst, RetT)
    , [{subtype, Env, ArgT, ArgFT} || {{_, ArgFT}, ArgT} <- lists:zip(ArgsFT, ArgsT)] ++
      S2
    };
constr_expr(Env, {'if', _, Cond, Then, Else}, T, S0) ->
    ExprT = ?refined(T, fresh_template("if")),
    {_, S1} = constr_expr(Env, Cond, S0),
    {ThenT, S2} = constr_expr(assert(Cond, Env), Then, S1),
    {ElseT, S3} = constr_expr(assert(?op('!', Cond), Env),Else, S2),
    { ExprT
    , [ {well_formed, Env, ExprT}
      , {subtype, assert(Cond, Env), ThenT, ExprT}
      , {subtype, assert(?op('!', Cond), Env), ElseT, ExprT}
      | S3
      ]
    };
constr_expr(Env, [E], _, S) ->
    constr_expr(Env, E, S);
constr_expr(Env0, [{letval, _, {typed, _, {id, _, Name}, VarT}, Val}|Rest], T, S0) ->
    DepVarT = ?refined(VarT, fresh_template(Name)),
    {ValT, S1} = constr_expr(Env0, Val, S0),
    Env1 = bind_var(Name, ValT, Env0),
    {RestT, S2} = constr_expr(Env1, Rest, T, S1),
    {DepVarT,
     [ {well_formed, Env0, DepVarT}
     , {subtype, Env1, RestT, DepVarT}
     | S2
     ]
    };
constr_expr(Env, [Expr|Rest], T, S0) ->
    {_, S1} = constr_expr(Env, Expr, S0),
    constr_expr(Env, Rest, T, S0);
constr_expr(Env, [], T, S) ->
    {T, S};
constr_expr(_, E, A, B) ->
    error({todo, E, A, B}).

%%%% Substitution

apply_subst1({id, _, X}, Expr, {id, _, X}) ->
    Expr;
apply_subst1({ltvar, X}, Expr, {ltvar, X}) ->
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

apply_subst(Subs, Q) when is_map(Subs) ->
    apply_subst(maps:to_list(Subs), Q);
apply_subst(Subs, Q) when is_list(Subs) ->
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
            Env1 = Env0#env{
                     type_binds =
                         maps:merge(maps:from_list([{Id, T} || {{id, _, Id}, T} <- ArgsSup]), Env0#env.type_binds)
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
            Env1 = Env0#env{
                     type_binds =
                         maps:merge(maps:from_list([{Id, T1} || {{id, _, Id}, T1} <- Args]), Env0#env.type_binds)
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

cmp_qualifiers(Thing) ->
    %% [].
    [ ?op(nu, '=<', Thing)
    , ?op(nu, '>=', Thing)
    , ?op(nu, '>', Thing)
    , ?op(nu, '<', Thing)
    ].

eq_qualifiers(Thing) ->
    [ ?op(nu, '==', Thing)
    , ?op(nu, '!=', Thing)
    ].

int_qualifiers(Thing) ->
    cmp_qualifiers(Thing) ++ eq_qualifiers(Thing).

plus_int_qualifiers({int, _, 0}, _Thing) -> [];
plus_int_qualifiers(Int, Thing) ->
    int_qualifiers(?op(Thing, '+', Int)) ++ int_qualifiers(?op(Thing, '-', Int)).

var_int_qualifiers(Var) ->
    int_qualifiers({id, ann(), Var}) ++ plus_int_qualifiers(?int(1), {id, ann(), Var}).

inst_pred_int(Scope) ->
    lists:concat(
      [ int_qualifiers(?int(0)) %% 0 is quite probable to be relevant
      , int_qualifiers(?int(1)) %% 1 as well
      , [ Q || {Var, {refined_t, _, ?int_tp, _}} <- Scope,
               Q <- var_int_qualifiers(Var)
        ]
      ]
     ).

inst_pred(BaseT, Scope) ->
    case BaseT of
        ?int_tp ->
            inst_pred_int(Scope);
        _ -> []
    end.

init_assg(Cs) ->
    lists:foldl(
      fun({well_formed, Env, {refined_t, _, BaseT, {template, _, LV}}}, Acc) ->
              AllQs = inst_pred(BaseT, maps:to_list(Env#env.type_binds)),
              ?DBG("INIT ASSG OF ~p:\n~s", [LV, aeso_pretty:pp(predicate, AllQs)]),
              Acc#{LV => #ltinfo{base = BaseT, env = Env, curr_qs = AllQs}};
         (X, Acc) -> Acc
      end, #{}, Cs).


group_subtypes(Cs) ->
    Subts = [C || C = {subtype, _, _, {refined_t, _, _, {template, _, _}}} <- Cs],
    WFs = Cs -- Subts,

    SubtsMap =
        lists:foldl(
          fun ({subtype, Env, T, {refined_t, _, _, {template, Subst, LV}}}, Map) ->
                  ?DBG("GROUPING SUB IN ~p\nOF\n~p\n:>\n~p", [Env, LV, T]),
                  maps:put(LV, [{Env, Subst, T}|maps:get(LV, Map, [])], Map)
          end, #{}, Subts
         ),
    WFs ++ [ {subtype, Ts, LV}
            || {LV, Ts} <- maps:to_list(SubtsMap)
           ].

assg_of(Assg, Var = {ltvar, _}) ->
    case maps:get(Var, Assg, undef) of
        undef ->
            #ltinfo
                { base = {id, ann(), "int"} %% FIXME NOT ONLY INT
                , curr_qs = []
                , env = init_env()
                };
        A -> A
    end.

pred_of(Assg, Var = {ltvar, _}) ->
    (assg_of(Assg, Var))#ltinfo.curr_qs;
pred_of(_, P) when is_list(P) ->
    P;
pred_of(Assg, {template, Subst, P}) ->
    apply_subst(Subst, pred_of(Assg, P));
pred_of(Assg, {refined_t, _, _, P}) ->
    pred_of(Assg, P).



solve(_Env, Cs) ->
    Assg0 = solve(init_assg(Cs), Cs, Cs),
    maps:map(fun
                 (K, V = #ltinfo{env = KEnv, base = Base, curr_qs = Qs}) ->
                     V#ltinfo{
                       curr_qs =
                           simplify_pred(
                             maps:put(nu, Base, KEnv#env.type_binds),
                             Qs
                            )
                      }
            end, Assg0).
solve(Assg, _, []) ->
    Assg;
solve(Assg, AllCs, [C|Rest]) ->
    ?DBG("SOLVING:\n~s", [aeso_pretty:pp(constr, C)]),
    case C of
        {subtype, _, R = {ltvar, _}} ->
            ?DBG("ASSG OF ~p: ~s", [R, aeso_pretty:pp(predicate, (assg_of(Assg, R))#ltinfo.curr_qs)]);
        _ -> ok
    end,
    case valid_in(C, Assg) of
        false -> ?DBG("CONSTR INVALID"),
                 Weakened = weaken(C, Assg),
                 solve(Weakened, AllCs, AllCs);
        true  -> ?DBG("CONSTR VALID"), solve(Assg, AllCs, Rest)
    end.

scope_pred(Assg, Scope) ->
    lists:concat(
      [ apply_subst1(nu, {id, ann(), Var}, pred_of(Assg, Pred))
        || {Var, {refined_t, _, _, Pred}} <- maps:to_list(Scope)
      ]).

valid_in({well_formed, _, _}, _) ->
    true; %% TODO
valid_in({subtype, Subs, SupPredVar} = C, Assg) ->
    Ltinfo = assg_of(Assg, SupPredVar),
    ?DBG("CHECKING VALID FOR COMP SUB\n~s", [aeso_pretty:pp(constr, C)]),
    lists:all(
      fun({#env{type_binds = Scope, path_pred = PathPred}, Subst, SubKVar}) ->
              ?DBG("SUBST IN VALID: ~p", [Subst]),
              VarPred = pred_of(Assg, SubKVar),
              ?DBG("SCOPE IN VALID: ~p", [Scope]),
              ScopePred = scope_pred(Assg, Scope),
              ?DBG("SCOPE PRED: ~s", [aeso_pretty:pp(predicate, ScopePred)]),
              SubPred = PathPred ++ VarPred ++ ScopePred,
              impl_holds(Scope, SubPred, apply_subst(Subst, Ltinfo#ltinfo.curr_qs))
      end,
      Subs
     );
valid_in({subtype, #env{type_binds = Scope, path_pred = PathPred},
          {refined_t, _, _, SubP}, {refined_t, _, _, SupP}} = C, Assg) when is_list(SupP) ->
    ?DBG("CHECKING VALID FOR RIGID SIMP SUB\n~s", [aeso_pretty:pp(constr, C)]),
    ScopePred = scope_pred(Assg, Scope),
    SubPred = PathPred ++ pred_of(Assg, SubP) ++ ScopePred,
    case impl_holds(Scope, SubPred, pred_of(Assg, SupP)) of
        true -> ok;
        false ->
            ?DBG("**** CONTRADICTION"),
            throw(contradict)
    end,
    true; %% TODO !!!! TODO what to do?
valid_in({subtype, _, T, T}, _) ->
    true.

weaken({subtype, Subs, SubPredVar}, Assg) ->
    ?DBG("**** WEAKENING SUB FOR ~p", [SubPredVar]),
    Ltinfo = assg_of(Assg, SubPredVar),
    Filtered =
        [ Q || Q <- Ltinfo#ltinfo.curr_qs,
               lists:all(fun({Env, Subst, Sub}) ->
                                 ?DBG("CHECKING SUB"),
                                 Valid = subtype_implies(Env, Sub, apply_subst(Subst, Q), Assg),
                                 ?DBG("ENV: ~p", [Env]),
                                 case Valid of
                                     true -> ?DBG("SUB VALID");
                                     false -> ?DBG("SUB INVALID")
                                 end,
                                 Valid
                         end, Subs)
        ],
    ?DBG("**** WEAKENED\n* FROM ~s\n* TO ~s",
         [aeso_pretty:pp(predicate, Ltinfo#ltinfo.curr_qs), aeso_pretty:pp(predicate, Filtered)]),
    NewLtinfo = Ltinfo#ltinfo{
                 curr_qs = Filtered
                },
    Assg#{SubPredVar => NewLtinfo}.

subtype_implies(#env{type_binds=Scope, path_pred=PathPred},
                {refined_t, _, _, Template}, Q, Assg
               ) ->
    SubPred =
        case Template of
            {template, Subst, KVar} ->
                apply_subst(Subst, (assg_of(Assg, KVar))#ltinfo.curr_qs);
            P -> P
        end,
    ?DBG("SCOPE: ~p\n", [Scope]),
    ScopePred = scope_pred(Assg, Scope),
    LPred = SubPred ++ ScopePred ++ PathPred,
    impl_holds(Scope, LPred, Q).


make_conjunction([]) -> {bool, ann(), true};
make_conjunction([H|T]) ->
    lists:foldl(
      fun (E, Acc) -> ?op(E, '&&', Acc)
      end, H, T);
make_conjunction(X) -> X.

impl_holds(Scope, Assump, Concl) when is_map(Scope) ->
    impl_holds(maps:to_list(Scope), Assump, Concl);
impl_holds(_, _, []) -> true;
impl_holds(Scope, Assump, Concl) when is_list(Scope) ->
    ConclExpr  = make_conjunction(Concl),
    ?DBG("IMPL;\n* ASSUMPTION: ~s\n* CONCLUSION: ~s", [aeso_pretty:pp(expr, make_conjunction(Assump)), aeso_pretty:pp(expr, ConclExpr)]),
    aeso_smt:scoped(
      fun() ->
              [aeso_smt:declare_const({var, Var}, type_to_smt(T))
               || {Var, T} <- Scope, element(1, T) =/= dep_fun_t
              ],
              aeso_smt:declare_const({var, "nu__"}, {var, "Int"}), %% FIXME
              [ aeso_smt:assert(expr_to_smt(Expr))
                || Expr <- Assump
              ],
              aeso_smt:assert(expr_to_smt(?op('!', ConclExpr))),
              Res = not aeso_smt:check_sat(),
              case Res of
                  true -> ?DBG("TRUE");
                  false  -> ?DBG("FALSE")
              end,
              Res
      end).

type_to_smt({refined_t, _, T, _}) ->
    type_to_smt(T);
type_to_smt(?int_tp) ->
    {var, "Int"};
type_to_smt(T) ->
    error({not_smt_type, T}).

is_smt_expr(Expr) ->
    try expr_to_smt(Expr) of
        _ -> true
    catch throw:_ ->
            false
    end.

expr_to_smt({id, _, Var}) ->
    {var, Var};
expr_to_smt({qid, _, QVar}) ->
    {var, string:join(QVar, "__")};
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
expr_to_smt(nu) -> {var, "nu__"};
expr_to_smt(E) -> throw({not_smt_expr, E}).

apply_assg(Assg, Var = {ltvar, _}) ->
    case Assg of
        #{Var := #ltinfo{curr_qs = P}} ->
            P;
        _ -> []
    end;
apply_assg(Assg, {template, S, T}) ->
    apply_assg(Assg, apply_subst(S, T));
apply_assg(Assg, [H|T]) -> [apply_assg(Assg, H)|apply_assg(Assg, T)];
apply_assg(Assg, T) when is_tuple(T) ->
    list_to_tuple(apply_assg(Assg, tuple_to_list(T)));
apply_assg(_, X) -> X.

%% this is absolutely heuristic
simplify_pred(Scope, Pred) ->
    simplify_pred(Scope, [], Pred).
simplify_pred(_Scope, Prev, []) ->
    Prev;
simplify_pred(Scope, Prev, [Q|Post]) ->
    case impl_holds(Scope, Prev ++ Post, Q) of
        true ->
            simplify_pred(Scope, Prev, Post);
        false ->
            simplify_pred(Scope, [Q|Prev], Post)
    end.

a_normalize(Expr = {typed, Ann, _, Type}) ->
    {Expr1, Decls} = a_normalize(Expr, []),
    case Decls of
        [] -> Expr1;
        _ -> ?typed({block, ann(), lists:reverse([Expr1|Decls])}, Type)
    end.

a_normalize({typed, Ann, Expr, Type}, Decls) ->
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
a_normalize_list([Expr|Rest], Acc, Decls0) ->
    {Expr1, Decls1} = a_normalize(Expr, Decls0),
    a_normalize_list(Rest, [Expr1|Acc], Decls1).


a_normalize_to_simpl({typed, Ann, Expr, Type}, Decls) ->
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
