%%% -*- erlang-indent-level:4; indent-tabs-mode: nil -*-
%%%-------------------------------------------------------------------
%%% @doc Test Sophia liquid type system.
%%%
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_type_refinement_tests).

-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").

setup() ->
    io:format("STARGIN... "),
    aeso_smt:start_z3(),
    aeso_ast_refine_types:init_refiner(),
    ok.

unsetup(_) ->
    io:format("STUPP"),
    aeso_smt:stop_z3(),
    ok.

hagia_test_() ->
    {inorder,
     {foreach, local, fun setup/0, fun unsetup/1,
      [ {timeout, 10, smt_solver_test_group()}
      , {timeout, 10, refiner_test_group()}
      ]
     }
    }.

smt_solver_test_group() ->
    [ { "x == x"
      , fun() ->
                io:format("aAAA"),
                ?assert(aeso_ast_refine_types:impl_holds(
                          aeso_ast_refine_types:bind_var(
                            {id, [], "x"}, {id, [], "int"},
                            aeso_ast_refine_types:init_env()),
                          [],
                          [{app, [], {'==', []}, [{id, [], "x"}, {id, [], "x"}]}]))
        end
      }
    ].

refiner_test_group() ->
    [ {"Testing liquid template generation of " ++ ContractName,
       fun() ->
               try run_refine(ContractName) of
                   {ok, AST} ->
                       io:format("~s", [aeso_pretty:pp(decls, AST)]), error(success);
                   {error, {contradict, Assump, Promise}} ->
                       io:format("Could not prove the promise\n  ~s\n"
                                    "from the assumption\n  ~s\n",
                                 [aeso_pretty:pp(predicate, Promise), aeso_pretty:pp(predicate, Assump)]
                                ),
                       error(contradict);
                   {error, ErrBin} ->
                       io:format("\n~s", [ErrBin]),
                       error(ErrBin)
               catch E:T:S -> io:format("\n\n\n***** CHUJ 8===>\n~p: ~p\nstack:\n~p\n", [E, T, S]), error(T)
               end
       end} || ContractName <- compilable_contracts()].


run_refine(Name) ->
    io:format("no elo\n\n"),
    ContractString = aeso_test_utils:read_contract(Name),
    Ast = aeso_parser:string(ContractString, sets:new(), []),
    {_, _, TAst} = aeso_ast_infer_types:infer(Ast, [return_env]),
    RAst = aeso_ast_refine_types:refine_ast(TAst),
    RAst.

%% compilable_contracts() -> [ContractName].
%%  The currently compilable contracts.
compilable_contracts() -> ["hagia"].
