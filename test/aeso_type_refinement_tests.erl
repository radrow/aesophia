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
                       io:format("~s", [aeso_pretty:pp(decls, AST)]), error(success);
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
    RAst = aeso_ast_refine_types:refine_ast(TAst),
    {ok, RAst}.

%% compilable_contracts() -> [ContractName].
%%  The currently compilable contracts.
compilable_contracts() -> ["hagia"].
