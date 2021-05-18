%%% -*- erlang-indent-level:4; indent-tabs-mode: nil -*-
%%%-------------------------------------------------------------------
%%% @doc Test Sophia liquid type system.
%%%
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_type_refinement_tests).

-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").

run_test(Test) ->
    TestFun = list_to_atom(lists:concat([Test, "_test_"])),
    [ begin
          io:format("~s\n", [Label]),
          Fun()
      end || {Label, Fun} <- ?MODULE:TestFun() ],
    ok.

solver_test_() ->
    aeso_smt:start_z3(),
    [ { "SMT solver test"
      , fun() ->
              ?assert(aeso_ast_refine_types:impl_holds(
                        aeso_ast_refine_types:bind_var(
                          {id, [], "x"}, {id, [], "int"},
                          aeso_ast_refine_types:init_env()),
                        [],
                        [{app, [], {'==', []}, [{id, [], "x"}, {id, [], "x"}]}]))
      end
      }
    ].

constraints_gen_test_() ->
    aeso_ast_refine_types:init_refiner(),
    [ {"Testing liquid template generation of " ++ ContractName,
       fun() ->
               try gen_constraints(ContractName) of
                   {ok, AST} ->
                       io:format("~p", [AST]), error(success);
                   {error, ErrBin} ->
                       io:format("\n~s", [ErrBin]),
                       error(ErrBin)
               catch E:T:S -> io:format("\n\n\n***** CHUJ 8===>\n~p: ~p\nstack:\n~p\n", [E, T, S]), error(T)
               end
           end} || ContractName <- compilable_contracts()].
gen_constraints(Name) ->
    io:format("no elo\n\n"),
    ContractString = aeso_test_utils:read_contract(Name),
    Ast = aeso_parser:string(ContractString, sets:new(), []),
    {_, _, TAst} = aeso_ast_infer_types:infer(Ast, [return_env]),
    [ begin
          InitEnv = aeso_ast_refine_types:init_env(),
          {Env, {contract, _, _, Defs}, Cs} = aeso_ast_refine_types:constr_con(InitEnv, Con),
          Cs1 = aeso_ast_refine_types:simplify(Cs),
          Cs2 = aeso_ast_refine_types:group_subtypes(Cs1),
          Assg = aeso_ast_refine_types:solve(Env, Cs2),
          io:format("\n\n**** EXTERNAL:\n"),
          [ io:format("~s : ~s\n", [aeso_pretty:pp(expr, Expr), aeso_pretty:pp(dep_type, aeso_ast_refine_types:apply_assg(Assg, T))])
           || {Expr, T} <- aeso_ast_refine_types:type_binds(Env)
          ],
          io:format("\n\n**** INTERNAL:\n"),
          [ io:format("_ : ~s\n", [aeso_pretty:pp(decl, aeso_ast_refine_types:apply_assg(Assg, T))])
            || T <- Defs
          ]
      end
     || Con <- TAst
    ],
    %% [ begin
    %%       {T, Cs} = aeso_ast_refine_types:constr_letfun(aeso_ast_refine_types:init_type_env(), Decl, []),
    %%       io:format("\n*** INFERRED\n\n~s\n\n",
    %%                 [prettypr:format(aeso_pretty:dep_type(T))
    %%                 ]),
    %%       Cs1 = aeso_ast_refine_types:simplify(Cs),
    %%       Cs2 = aeso_ast_refine_types:group_subtypes(Cs1),
    %%       io:format("**** CONSTRAINTS ****\n\n"),
    %%       [io:format("~s\n\n", [prettypr:format(aeso_pretty:constr(C))]) || C <- Cs],
    %%       Assg = aeso_ast_refine_types:solve(Cs2),
    %%       T1 = aeso_ast_refine_types:apply_assg(Assg, T),
    %%       io:format("**** SOLVED ****\n\n~s\n", [aeso_pretty:pp(dep_type, T1)])
    %%   end
    %%   || {contract, _, _, Decls} <- TAst,
    %%      Decl <- Decls,
    %%     element(1, Decl) =:= letfun
    %% ],
    {ok, ok}.

%% compilable_contracts() -> [ContractName].
%%  The currently compilable contracts.
compilable_contracts() -> ["hagia"].
