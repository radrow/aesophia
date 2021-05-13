-module(aeso_ast_refine_types).
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
        , interesting_integers :: [integer()]
        }).
-type type_env() :: #type_env{}.

-type constr() :: {subtype, type_env(), template(), template()}
                | {well_formed, type_env(), template()}.

%% Grouped subtype
-type subtype_constr() :: {subtype, [{type_env(), subst(), template()}], ltvar()}.

-record(kinfo, {base :: aeso_syntax:type(), curr_qs :: predicate(), env :: type_env()}).
-type kinfo() :: #kinfo{}.

-type variance() :: contravariant | covariant.

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
       type_binds =
           #{%"value" => {refined_t, ann(), {id, ann(), "int"}, [{app, ann(), {'>=', ann()}, [nu, {int, ann(), 123}]}]}
           },
       path_pred = [],
       interesting_integers = [0, 1]
      }.

-spec fresh_ltvar(string()) -> ltvar().
fresh_ltvar(Name) ->
    I = get(ltvar_supply),
    put(ltvar_supply, I + 1),
    {ltvar, Name ++ "_" ++ integer_to_list(I)}.

-spec fresh_template(string()) -> template().
fresh_template(Name) -> fresh_template(covariant, Name).
fresh_template(covariant, Name) -> {template, [], fresh_ltvar(Name)};
fresh_template(contravariant, Name) -> [].

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

switch_variance(covariant) ->
    contravariant;
switch_variance(contravariant) ->
    covariant.

%% Decorates base types with templates through the AST
decorate_base_types(Hint, Type) ->
    decorate_base_types(covariant, Hint, Type).
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

constr_con({contract, Ann, Con, Defs}) ->
    EnvDefs =
        maps:from_list(
          [ begin
                ArgsT =
                    [ {ArgName, decorate_base_types(contravariant, "arg_" ++ StrName, T)}
                      || {typed, _, ArgName = {id, _, StrName}, T} <- Args
                    ],
                TypeDep = {dep_fun_t, FAnn, [], ArgsT, decorate_base_types("ret", RetT)},
                {Name, TypeDep}
            end
            || {letfun, FAnn, {id, _, Name}, Args, RetT, _} <- Defs
          ]),
    Env1 = #type_env{type_binds = EnvDefs, path_pred = []},
    {Defs1, Ss} = lists:unzip(
                   [constr_letfun(Env1, Def, []) || Def <- Defs]
                  ),
    S = lists:flatten(Ss),
    {{contract, Ann, Con, Defs1}, Env1, S}.

constr_letfun(Env0, {letfun, Ann, {id, _, Name}, Args, RetT, Body}, S) ->
    ArgsT =
        [ {ArgName, decorate_base_types(contravariant, "argi_" ++ StrName, T)}
          || {typed, _, ArgName = {id, _, StrName}, T} <- Args
        ],
    Env1 = bind_args(ArgsT, Env0),
    {DepRetT, S1} = constr_expr(Env1, Body, S),
    DepSelfT =
        { dep_fun_t, Ann, []
        , ArgsT
        , DepRetT
        },
    GlobalFunType = maps:get(Name, Env0#type_env.type_binds),
    S2 = [ {subtype, Env1, DepSelfT, GlobalFunType}
         , {well_formed, Env1, GlobalFunType}
         | S1
         ],

    {DepSelfT, S2}.


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
            ?DBG("UNDEF VAR ~s", [Name]),
            Eq = ?op(nu, '==', Expr),
            {{refined_t, ann(), T, [Eq]}, S};
        {refined_t, Ann, B, P} = T1 ->
            Eq = ?op(nu, '==', Expr), %% IF THIS IS THE ONLY Q THEN IT WORKS BETTER
            { {refined_t, Ann, B, [Eq]}
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
       ], ?refined(RetT, [?op(nu, '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
      }
    , S
    };
constr_expr(_Env, Expr = {'-', Ann}, ?int_tp, S) ->
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
      [{well_formed, Env, ExprT} | S2]
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

cmp_qualifiers(Thing) ->
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

inst_pred_int(Scope) ->
    lists:concat(
      [ int_qualifiers(?int(0)) %% 0 is quite probable to be relevant
      %% , int_qualifiers(?int(1)) %% 1 as well
      , [ Q || {Var, {refined_t, _, ?int_tp, _}} <- Scope,
               Q <- int_qualifiers({id, ann(), Var})
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
              AllQs = inst_pred(BaseT, maps:to_list(Env#type_env.type_binds)),
              Acc#{LV => #kinfo{base = BaseT, env = Env, curr_qs = AllQs}};
         (X, Acc) -> Acc
      end, #{}, Cs).


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
                { base = {id, ann(), "int"} %% FIXME NOT ONLY INT
                , curr_qs = []
                , env = init_type_env()
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



solve(_Env, Cs) ->
    Assg0 = solve(init_assg(Cs), Cs, Cs),
    maps:map(fun
                 (K, V = #kinfo{env = KEnv, base = Base, curr_qs = Qs}) ->
                     ?DBG("SIMPLIFYNIG ~p", [K]),
                     V#kinfo{
                       curr_qs =
                           simplify_pred(
                             maps:put(nu, Base, KEnv#type_env.type_binds),
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
            ?DBG("ASSG OF ~p: ~s", [R, aeso_pretty:pp(predicate, (assg_of(Assg, R))#kinfo.curr_qs)]);
        _ -> ok
    end,
    case valid_in(C, Assg) of
        false -> ?DBG("CONSTR INVALID"),
                 Weakened = weaken(C, Assg),
                 solve(Weakened, AllCs, AllCs);
        true  -> ?DBG("CONSTR VALID"), solve(Assg, AllCs, Rest)
    end.

valid_in({well_formed, _, _}, _) ->
    true; %% TODO
valid_in({subtype, Subs, SupPredVar} = C, Assg) ->
    KInfo = assg_of(Assg, SupPredVar),
    ?DBG("CHECKING VALID FOR COMP SUB\n~s", [aeso_pretty:pp(constr, C)]),
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
          {refined_t, _, _, SubP}, {refined_t, _, _, SupP}} = C, Assg) when is_list(SupP) ->
    ?DBG("CHECKING VALID FOR RIGID SIMP SUB\n~s", [aeso_pretty:pp(constr, C)]),
    ScopePred = [], %% TODO
    SubPred = PathPred ++ pred_of(Assg, SubP) ++ ScopePred,
    case impl_holds(Scope, SubPred, pred_of(Assg, SupP)) of
        true -> ok;
        false ->
            ?DBG("**** CONTRADICTION"),
            throw(contradict)
    end,
    true. %% TODO !!!!

weaken({subtype, Subs, SubPredVar}, Assg) ->
    ?DBG("**** WEAKENING SUB FOR ~p", [SubPredVar]),
    KInfo = assg_of(Assg, SubPredVar),
    Filtered =
        [ Q || Q <- KInfo#kinfo.curr_qs,
               lists:all(fun({Env, Subst, Sub}) ->
                                 ?DBG("CHECKING SUB"),
                                 Valid = subtype_implies(Env, Sub, apply_subst(Subst, Q), Assg),
                                 case Valid of
                                     true -> ?DBG("SUB VALID");
                                     false -> ?DBG("SUB INVALID")
                                 end,
                                 Valid
                         end, Subs)
        ],
    ?DBG("**** WEAKENED\n* FROM ~s\n* TO ~s",
         [aeso_pretty:pp(predicate, KInfo#kinfo.curr_qs), aeso_pretty:pp(predicate, Filtered)]),
    NewKInfo = KInfo#kinfo{
                 curr_qs = Filtered
                },
    Assg#{SubPredVar => NewKInfo}.

subtype_implies(#type_env{type_binds=Scope, path_pred=PathPred},
                {refined_t, _, _, Template}, Q, Assg
               ) ->
    SubPred =
        case Template of
            {template, _Subst, KVar} -> %% TODO Why do we skip Subst?
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

impl_holds(Scope, Assump, Concl) when is_map(Scope) ->
    impl_holds(maps:to_list(Scope), Assump, Concl);
impl_holds(_, _, []) -> true;
impl_holds(Scope, Assump, Concl) when is_list(Scope) ->
    ConclExpr  = make_conjunction(Concl),
    %% ?DBG("SCOPE:\n~p", [Scope]),
    ?DBG("IMPL;\n* ASSUMPTION: ~s\n* CONCLUSION: ~s", [aeso_pretty:pp(expr, make_conjunction(Assump)), aeso_pretty:pp(expr, ConclExpr)]),
    aeso_smt:scoped(
      fun() ->
              [try aeso_smt:declare_const({var, Var}, type_to_smt(T)) %% FIXME this is cancer
               catch _:_ -> %%?DBG("BAD VAR ~p : ~p", [Var, T])
                       ok
               end
               || {Var, T} <- Scope
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
    error({type_not_smtable, T}).

is_smt_expr(Expr) ->
    try expr_to_smt(Expr) of
        _ -> true
    catch throw:_ ->
            false
    end.

expr_to_smt({id, _, Var}) ->
    {var, Var};
expr_to_smt({qid, _, L}) ->
    {var, lists:last(L)}; %% FIXME
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
        #{Var := #kinfo{curr_qs = P}} ->
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
%% simplify_pred(Scope, Pred) -> Pred;
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
