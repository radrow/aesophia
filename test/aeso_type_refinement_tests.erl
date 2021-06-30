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
    erlang:system_flag(backtrace_depth, 100),
    aeso_smt:start_z3(),
    aeso_ast_refine_types:init_refiner(),
    ok.

unsetup(_) ->
    aeso_smt:stop_z3(),
    ok.

hagia_test_() ->
    {inorder,
     {foreach, local, fun setup/0, fun unsetup/1,
      [ {timeout, 5, smt_solver_test_group()}
      , {timeout, 40, refiner_test_group()}
      ]
     }
    }.

smt_solver_test_group() ->
    [ { "x == x"
      , fun() ->
                ?assert(aeso_ast_refine_types:impl_holds(
                          aeso_ast_refine_types:bind_var(
                            {id, [], "x"}, {id, [], "int"},
                            aeso_ast_refine_types:init_env(undefined)),
                          [],
                          [{app, [], {'==', []}, [{id, [], "x"}, {id, [], "x"}]}]))
        end
      }
    ].

refiner_test_group() ->
    [ {"Testing type refinement of " ++ ContractName,
       fun() ->
               try {run_refine("hagia/" ++ ContractName), Expect} of
                   {{ok, AST}, {success, Assertions}} ->
                       io:format("AST:\n~s\n\n", [aeso_pretty:pp(decls, AST)]),
                       check_ast_refinement(AST, Assertions);
                   {{error, Err}, _} ->
                       io:format(aeso_ast_refine_types:pp_error(Err)),
                       error(Err)
               catch E:T:S -> io:format("Caught:\n~p: ~p\nstack:\n~p\n", [E, T, S]), error(T)
               end
       end} || {ContractName, Expect} <- compilable_contracts()].


run_refine(Name) ->
    ContractString = aeso_test_utils:read_contract(Name),
    Ast = aeso_parser:string(ContractString, sets:new(), []),
    {TEnv, TAst, _} = aeso_ast_infer_types:infer(Ast, [return_env, dont_unfold]),
    RAst = aeso_ast_refine_types:refine_ast(TEnv, TAst),
    RAst.

check_ast_refinement(AST, Assertions) ->
    [ case maps:get({Name, FName}, Assertions, unchecked) of
          unchecked -> ok;
          ExType -> check_type(ExType, Type)
      end
     || {_, _, {con, _, Name}, Defs} <- AST,
        {fun_decl, _, {id, _, FName}, Type} <- Defs
    ].

check_type(ExQuals, {dep_fun_t, _, _, _, {refined_t, _, _, Quals}}) ->
    ?assertEqual(ExQuals, aeso_pretty:pp(predicate, Quals)).

%% compilable_contracts() -> [ContractName].
%%  The currently compilable contracts.
compilable_contracts() ->
    [ {"test",
       {success,
        #{{"Test", "f"} => something}
       }
      }
     %% , {"max",
     %%  {success,
     %%   #{{"C", "max"} => "$nu >= b && $nu >= a"
     %%   , {"C", "trim"} => "$nu > -1 && $nu >= x"
     %%   }
     %%  }
     %% }
    ].
