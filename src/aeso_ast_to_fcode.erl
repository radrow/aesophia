%%%-------------------------------------------------------------------
%%% @author Ulf Norell
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     Compiler from Aeterinty Sophia language to Fate intermediate code.
%%% @end
%%% Created : 26 Mar 2019
%%%
%%%-------------------------------------------------------------------
-module(aeso_ast_to_fcode).

-export([ast_to_fcode/2]).
-export_type([fcode/0, fexpr/0, fun_def/0]).

%% -- Type definitions -------------------------------------------------------

-type option() :: none().

-type attribute() :: stateful | pure.

-type fun_name() :: {entrypoint, binary()}
                  | {local_fun, [string()]}
                  | init.
-type var_name() :: string().
-type sophia_name() :: [string()].

-type binop() :: '+' | '-' | '=='.

-type fexpr() :: {integer, integer()}
               | {bool, false | true}
               | {var, var_name()}
               | {binop, ftype(), binop(), fexpr(), fexpr()}
               | {'if', fexpr(), fexpr(), fexpr()}
               | {'let', var_name(), fexpr(), fexpr()}
               | {switch, fcase()}.

-type fcase() :: {split, ftype(), var_name(), [fsplit_case()], fdefault()}
               | {nosplit, [var_name()], fexpr()}.

-type fsplit_case() :: {'case', fsplit_pat(), fcase()}.
-type fsplit_pat()  :: {tuple, [var_name()]}.

-type fdefault() :: nodefault | {default, fcase()}.

%% Intermediate format before case trees (fcase() and fsplit()).
-type falt() :: {'case', [fpat()], fexpr()}.
-type fpat() :: {var, var_name()}
              | {tuple, [fpat()]}.

-type ftype() :: aeb_fate_data:fate_type_type().


-type fun_def() :: #{ attrs  := [attribute()],
                      args   := [{var_name(), ftype()}],
                      return := ftype(),
                      body   := fexpr() }.

-type fcode() :: #{ contract_name := string(),
                    state_type    := ftype(),
                    event_type    := ftype() | none,
                    functions     := #{ fun_name() => fun_def() } }.

-type type_env() :: #{ sophia_name() => fun(([ftype()]) -> ftype()) }.
-type fun_env()  :: #{ sophia_name() => fun_name() }.

-type context() :: {main_contract, string()}
                 | {namespace, string()}
                 | {abstract_contract, string()}.

-type env() :: #{ type_env  := type_env(),
                  fun_env   := fun_env(),
                  options   := [],
                  context   => context(),
                  functions := #{ fun_name() => fun_def() } }.

%% -- Entrypoint -------------------------------------------------------------

%% Main entrypoint. Takes typed syntax produced by aeso_ast_infer_types:infer/1,2
%% and produces Fate intermediate code.
-spec ast_to_fcode(aeso_syntax:ast(), [option()]) -> fcode().
ast_to_fcode(Code, Options) ->
    to_fcode(init_env(Options), Code).

%% -- Environment ------------------------------------------------------------

-spec init_env([option()]) -> env().
init_env(Options) ->
    #{ type_env  => init_type_env(),
       fun_env   => #{},    %% TODO: builtin functions here?
       options   => Options,
       functions => #{} }.

-define(type(T),       fun([])     -> T end).
-define(type(X, T),    fun([X])    -> T end).
-define(type(X, Y, T), fun([X, Y]) -> T end).

-spec init_type_env() -> type_env().
init_type_env() ->
    #{ ["int"]          => ?type(integer),
       ["bool"]         => ?type(boolean),
       ["bits"]         => ?type(bits),
       ["string"]       => ?type(string),
       ["address"]      => ?type(address),
       ["hash"]         => ?type(hash),
       ["signature"]    => ?type(signature),
       ["oracle"]       => ?type(_, _, oracle),
       ["oracle_query"] => ?type(_, _, oracle_query),    %% TODO: not in Fate
       ["list"]         => ?type(T, {list, T}),
       ["map"]          => ?type(K, V, {map, K, V}),
       ["option"]       => ?type(T, {variant, [[], [T]]}),
       ["Chain", "ttl"] => ?type({variant, [[integer], [integer]]})
     }.

%% -- Compilation ------------------------------------------------------------

-spec to_fcode(env(), aeso_syntax:ast()) -> fcode().
to_fcode(Env, [{contract, _, {con, _, Main}, Decls}]) ->
    #{ functions := Funs } = Env1 =
        decls_to_fcode(Env#{ context => {main_contract, Main} }, Decls),
    StateType = lookup_type(Env1, [Main, "state"], [], {tuple, []}),
    EventType = lookup_type(Env1, [Main, "event"], [], none),
    #{ contract_name => Main,
       state_type    => StateType,
       event_type    => EventType,
       functions     => Funs };
to_fcode(Env, [{contract, _, {con, _, Con}, Decls} | Code]) ->
    Env1 = decls_to_fcode(Env#{ context => {abstract_contract, Con} }, Decls),
    to_fcode(Env1, Code);
to_fcode(Env, [{namespace, _, {con, _, Con}, Decls} | Code]) ->
    Env1 = decls_to_fcode(Env#{ context => {namespace, Con} }, Decls),
    to_fcode(Env1, Code).

-spec decls_to_fcode(env(), [aeso_syntax:decl()]) -> env().
decls_to_fcode(Env, Decls) ->
    %% First compute mapping from Sophia names to fun_names and add it to the
    %% environment.
    Env1 = add_fun_env(Env, Decls),
    lists:foldl(fun(D, E) ->
                    init_fresh_names(),
                    R = decl_to_fcode(E, D),
                    clear_fresh_names(),
                    R
                end, Env1, Decls).

-spec decl_to_fcode(env(), aeso_syntax:decl()) -> env().
decl_to_fcode(Env, {type_decl, _, _, _}) -> Env;
decl_to_fcode(Env, {fun_decl, _, _, _})  -> Env;
decl_to_fcode(Env, Decl = {type_def, _Ann, {id, _, _Name}, _Args, _Def}) ->
    error({todo, Decl}),
    Env;
decl_to_fcode(Env = #{ functions := Funs }, {letfun, Ann, {id, _, Name}, Args, Ret, Body}) ->
    Attrs = get_attributes(Ann),
    FName = lookup_fun(Env, qname(Env, Name)),
    FArgs = args_to_fcode(Env, Args),
    FBody = expr_to_fcode(Env, Body),
    Def   = #{ attrs  => Attrs,
               args   => FArgs,
               return => type_to_fcode(Env, Ret),
               body   => FBody },
    NewFuns = Funs#{ FName => Def },
    Env#{ functions := NewFuns }.

-spec type_to_fcode(env(), aeso_syntax:type()) -> ftype().
type_to_fcode(Env, {app_t, T = {Id, _, _}, Types}) when Id == id; Id == qid ->
    lookup_type(Env, T, [type_to_fcode(Env, Type) || Type <- Types]);
type_to_fcode(Env, T = {Id, _, _}) when Id == id; Id == qid ->
    lookup_type(Env, T, []);
type_to_fcode(Env, {tuple_t, _, Types}) ->
    {tuple, [type_to_fcode(Env, T) || T <- Types]};
type_to_fcode(_Env, Type) ->
    {todo, Type}.

-spec args_to_fcode(env(), [aeso_syntax:arg()]) -> [{var_name(), ftype()}].
args_to_fcode(Env, Args) ->
    [ {Name, type_to_fcode(Env, Type)} || {arg, _, {id, _, Name}, Type} <- Args ].

-spec expr_to_fcode(env(), aeso_syntax:expr()) -> fexpr().
expr_to_fcode(Env, {typed, _, Expr, Type}) ->
    expr_to_fcode(Env, type_to_fcode(Env, Type), Expr);
expr_to_fcode(Env, Expr) ->
    expr_to_fcode(Env, no_type, Expr).

-spec expr_to_fcode(env(), ftype() | no_type, aeso_syntax:expr()) -> fexpr().

%% Literals
expr_to_fcode(_Env, _Type, {int, _, N})  -> {integer, N};
expr_to_fcode(_Env, _Type, {bool, _, B}) -> {bool, B};

%% Variables
expr_to_fcode(_Env, _Type, {id, _, X}) -> {var, X};

%% Tuples
expr_to_fcode(Env, _Type, {tuple, _, Es}) ->
    {tuple, [expr_to_fcode(Env, E) || E <- Es]};

%% Conditionals
expr_to_fcode(Env, _Type, {'if', _, Cond, Then, Else}) ->
    {'if', expr_to_fcode(Env, Cond),
           expr_to_fcode(Env, Then),
           expr_to_fcode(Env, Else)};

%% Switch
expr_to_fcode(Env, _, {switch, _, Expr = {typed, _, _, Type}, Alts}) ->
    X = fresh_name(),
    {'let', X, expr_to_fcode(Env, Expr),
     {switch, alts_to_fcode(Env, type_to_fcode(Env, Type), X, Alts)}};

%% Blocks
expr_to_fcode(Env, _Type, {block, _, Stmts}) ->
    stmts_to_fcode(Env, Stmts);

%% Binary operator
expr_to_fcode(Env, Type, {app, _Ann, {Op, _}, [A, B]}) when is_atom(Op) ->
    FOp = binop_to_fcode(Op),
    {binop, Type, FOp, expr_to_fcode(Env, A), expr_to_fcode(Env, B)};

expr_to_fcode(_Env, Type, Expr) ->
    {todo, {Expr, ':', Type}}.

binop_to_fcode(Op) when Op == '+'; Op == '-'; Op == '==' -> Op.

-spec alts_to_fcode(env(), ftype(), var_name(), [aeso_syntax:alt()]) -> fcase().
alts_to_fcode(Env, Type, X, Alts) ->
    split_tree(Env, [{X, Type}], [alt_to_fcode(Env, Alt) || Alt <- Alts]).

%% Invariant: the number of variables matches the number of patterns in each falt.
-spec split_tree(env(), [{var_name(), ftype()}], [falt()]) -> fcase().
split_tree(_Env, [], [{'case', [], Expr}]) ->
    {nosplit, Expr};
split_tree(Env, Vars, Alts) ->
    case next_split(Alts) of
        {nosplit, Xs, Expr} -> {nosplit, Xs, Expr};
        {split, I, Splits} ->
            {Vars1, [{X, T} | Vars2]} = lists:split(I, Vars),
            Cases = [{'case', Pat, split_tree(Env, Vars1 ++ split_vars(Pat, T) ++ Vars2, As)}
                     || {Pat, As} <- Splits],
            {split, T, X, Cases, nodefault}
    end.

-spec split_vars(fsplit_pat(), ftype()) -> [{var_name(), ftype()}].
split_vars({tuple, Xs}, {tuple, Ts}) ->
    lists:zip(Xs, Ts).

%% TODO: catchalls
-spec next_split([falt()]) -> {nosplit, [var_name()], fexpr()} | {split, integer(), [{fsplit_pat(), [falt()]}]}.
next_split([]) ->
    {nosplit, {abort, <<"Non-exhaustive pattern">>}};
next_split(Alts = [{'case', Pats, Body} | _]) ->
    NotMatch  = fun({var, _}) -> true; (_) -> false end,
    case lists:splitwith(NotMatch, Pats) of
        {Vars, []} -> {nosplit, [X || {var, X} <- Vars], Body};
        {Vars, _} ->
            I = length(Vars),
            Splits = group_by_split_pat([ split_alt(I, Alt) || Alt <- Alts ]),
            {split, I, Splits}
    end.

-spec split_alt(integer(), falt()) -> {fsplit_pat() | default, falt()}.
split_alt(I, {'case', Pats, Body}) ->
    {Pats1, [Pat | Pats2]} = lists:split(I, Pats),
    {FPat, InnerPats} = split_pat(Pat),
    {FPat, {'case', Pats1 ++ InnerPats ++ Pats2, Body}}.

-spec split_pat(fpat()) -> {fsplit_pat() | default, [fpat()]}.
split_pat({var, X})      -> {default, [{var, X}]};
split_pat({tuple, Pats}) ->
    Var = fun({var, X}) -> X; (_) -> fresh_name() end,
    Xs = [Var(P) || P <- Pats],
    {{tuple, Xs}, Pats}.

-spec group_by_split_pat([{fsplit_pat() | default, falt()}]) -> [{fsplit_pat(), [falt()]}].
group_by_split_pat(Alts) ->
    Tag = fun(default)    -> default;
             ({tuple, _}) -> tuple end,
    Grouped = maps:values(lists:foldr(
        fun({Pat, _} = Alt, Map) ->
            maps:update_with(Tag(Pat), fun(As) -> [Alt | As] end, [Alt], Map)
        end, #{}, Alts)),
    [ {Pat, [As || {_, As} <- G]} || G = [{Pat, _} | _] <- Grouped ].

-spec alt_to_fcode(env(), aeso_syntax:alt()) -> falt().
alt_to_fcode(Env, {'case', _, Pat, Expr}) ->
    {'case', [pat_to_fcode(Env, Pat)], expr_to_fcode(Env, Expr)}.

-spec pat_to_fcode(env(), aeso_syntax:pattern()) -> fpat().
pat_to_fcode(Env, {typed, _, Pat, Type}) ->
    pat_to_fcode(Env, type_to_fcode(Env, Type), Pat);
pat_to_fcode(Env, Pat) ->
    pat_to_fcode(Env, no_type, Pat).

-spec pat_to_fcode(env(), ftype() | no_type, aeso_syntax:pattern()) -> fpat().
pat_to_fcode(_Env, _Type, {id, _, X}) -> {var, X};
pat_to_fcode(Env, _Type, {tuple, _, Pats}) ->
    {tuple, [ pat_to_fcode(Env, Pat) || Pat <- Pats ]};
pat_to_fcode(_Env, Type, Pat) -> {todo, Pat, ':', Type}.

-spec stmts_to_fcode(env(), [aeso_syntax:stmt()]) -> fexpr().
stmts_to_fcode(Env, [{letval, _, {typed, _, {id, _, X}, _}, _, Expr} | Stmts]) ->
    {'let', X, expr_to_fcode(Env, Expr), stmts_to_fcode(Env, Stmts)};

stmts_to_fcode(Env, [Expr]) ->
    expr_to_fcode(Env, Expr).

%% -- Optimisations ----------------------------------------------------------

%% - Translate && and || to ifte
%% - Deadcode elimination
%% - Unused variable analysis (replace by _)
%% - Simplified case trees (FATE has special instructions for shallow matching)
%% - Constant propagation

%% -- Helper functions -------------------------------------------------------

%% -- Types --

-spec lookup_type(env(), aeso_syntax:id() | aeso_syntax:qid() | sophia_name(), [ftype()]) -> ftype().
lookup_type(Env, {id, _, Name}, Args) ->
    lookup_type(Env, [Name], Args);
lookup_type(Env, {qid, _, Name}, Args) ->
    lookup_type(Env, Name, Args);
lookup_type(Env, Name, Args) ->
    case lookup_type(Env, Name, Args, not_found) of
        not_found -> error({unknown_type, Name});
        Type      -> Type
    end.

-spec lookup_type(env(), sophia_name(), [ftype()], ftype()) -> ftype().
lookup_type(#{ type_env := TypeEnv }, Name, Args, Default) ->
    case maps:get(Name, TypeEnv, false) of
        false -> Default;
        Fun   -> Fun(Args)
    end.

%% -- Names --

-spec add_fun_env(env(), [aeso_syntax:decl()]) -> fun_env().
add_fun_env(#{ context := {abstract_contract, _} }, _) -> #{};  %% no functions from abstract contracts
add_fun_env(Env = #{ fun_env := FunEnv }, Decls) ->
    Entry = fun({letfun, Ann, {id, _, Name}, _, _, _}) ->
                [{qname(Env, Name), make_fun_name(Env, Ann, Name)}];
               (_) -> [] end,
    FunEnv1 = maps:from_list(lists:flatmap(Entry, Decls)),
    Env#{ fun_env := maps:merge(FunEnv, FunEnv1) }.

make_fun_name(#{ context := Context }, Ann, Name) ->
    Private = proplists:get_value(private, Ann, false) orelse
              proplists:get_value(internal, Ann, false),
    case Context of
        {main_contract, Main} ->
            if Private        -> {local_fun, [Main, Name]};
               Name == "init" -> init;
               true           -> {entrypoint, list_to_binary(Name)}
            end;
        {namespace, Lib} ->
            {local_fun, [Lib, Name]}
    end.

-spec current_namespace(env()) -> string().
current_namespace(#{ context := Cxt }) ->
    case Cxt of
        {abstract_contract, Con} -> Con;
        {main_contract, Con}     -> Con;
        {namespace, NS}          -> NS
    end.

-spec qname(env(), string()) -> sophia_name().
qname(Env, Name) ->
    [current_namespace(Env), Name].

-spec lookup_fun(env(), sophia_name()) -> fun_name().
lookup_fun(#{ fun_env := FunEnv }, Name) ->
    case maps:get(Name, FunEnv, false) of
        false -> error({unbound_name, Name});
        FName -> FName
    end.

init_fresh_names() ->
    put('%fresh', 0).

clear_fresh_names() ->
    erase('%fresh').

-spec fresh_name() -> var_name().
fresh_name() ->
    N = get('%fresh'),
    put('%fresh', N + 1),
    lists:concat(["%", N]).

%% -- Attributes --

get_attributes(Ann) ->
    [stateful || proplists:get_value(stateful, Ann, false)].

