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
    [ {"Testing type refinement of " ++ ContractName,
       fun() ->
               try {run_refine("hagia/" ++ ContractName), Expect} of
                   {{ok, AST}, {success, Assertions}} ->
                       io:format("AST:\n~s\n\n", [aeso_pretty:pp(decls, AST)]),
                       check_ast_refinement(AST, Assertions);
                   {{error, {contradict, Assump, Promise}}, {contradict, ExAssump, ExPromise}} ->
                       ?assertEqual(ExAssump, Assump),
                       ?assertEqual(ExPromise, Promise);
                   {{error, {contradict, Ann, Assump, Promise}}, _} ->
                       io:format("Could not prove the promise created at ~s ~p:~p\n"
                                 "~s:\n"
                                 "  ~s\n"
                                 "from the assumption\n"
                                 "  ~s\n",
                                 [aeso_syntax:get_ann(file, Ann, ""),
                                  aeso_syntax:get_ann(line, Ann, 0),
                                  aeso_syntax:get_ann(col, Ann, 0),
                                  pp_context(aeso_syntax:get_ann(context, Ann, none)),
                                  aeso_pretty:pp(predicate, Promise),
                                  aeso_pretty:pp(predicate, Assump)]
                                ),
                       error(contradict);
                   {{error, {invalid_reachable, Ann, Pred}}, _} ->
                       io:format("Could not ensure safety of the control flow at ~s ~p:~p\n"
                                 "by proving that\n"
                                 "  ~s\n"
                                 "never holds.",
                                 [aeso_syntax:get_ann(file, Ann, ""),
                                  aeso_syntax:get_ann(line, Ann, 0),
                                  aeso_syntax:get_ann(col, Ann, 0),
                                  aeso_pretty:pp(predicate, Pred)
                                 ]
                                ),
                       error(invalid_reachable);
                   {{error, {valid_unreachable, Ann, Pred}}, _} ->
                       io:format("Found dead code at ~s ~p:~p\n"
                                 "by proving that\n"
                                 "  ~s\n"
                                 "never holds.",
                                 [aeso_syntax:get_ann(file, Ann, ""),
                                  aeso_syntax:get_ann(line, Ann, 0),
                                  aeso_syntax:get_ann(col, Ann, 0),
                                  aeso_pretty:pp(predicate, Pred)
                                 ]
                                ),
                       error(valid_unreachable);
                   {{error, {overwrite, Id}}, _} ->
                       io:format("Illegal redefinition of the variable ~s at ~s ~p:~p",
                                 [aeso_syntax:pp(expr, Id),
                                  aeso_syntax:get_ann(file, Id, ""),
                                  aeso_syntax:get_ann(line, Id, 0),
                                  aeso_syntax:get_ann(col, Id, 0)
                                 ]
                                ),
                       error(overwrite);
                   {{error, ErrBin}, _} ->
                       io:format("\n~s", [ErrBin]),
                       error(ErrBin)
               catch E:T:S -> io:format("Caught:\n~p: ~p\nstack:\n~p\n", [E, T, S]), error(T)
               end
       end} || {ContractName, Expect} <- compilable_contracts()].


run_refine(Name) ->
    ContractString = aeso_test_utils:read_contract(Name),
    Ast = aeso_parser:string(ContractString, sets:new(), []),
    {_, _, TAst} = aeso_ast_infer_types:infer(Ast, [return_env]),
    RAst = aeso_ast_refine_types:refine_ast(TAst),
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
        #{{"C", "f"} => something}
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


pp_context(none) ->
    "";
pp_context({app, Ann, {typed, _, Fun, _}, N}) ->
    io_lib:format(
      "arising from an application of ~p to its ~s argument",
      [ aeso_pretty:pp(expr, Fun)
      , case aeso_syntax:get_ann(format, Ann, prefix) of
            prefix -> case abs(N rem 10) of
                          1 -> integer_to_list(N) ++ "st";
                          2 -> integer_to_list(N) ++ "nd";
                          3 -> integer_to_list(N) ++ "rd";
                          _ -> integer_to_list(N) ++ "th"
                      end;
            infix -> case N of
                         1 -> "left";
                         2 -> "right"
                     end
        end
      ]);
pp_context(then) ->
    "arising from the assumption of the `if` condition";
pp_context(else) ->
    "arising from the negation of the `if` condition";
pp_context({switch, N}) ->
    io_lib:format(
      "arising from the assumption of triggering of the ~s branch of `switch`",
      case abs(N rem 10) of
          1 -> integer_to_list(N) ++ "st";
          2 -> integer_to_list(N) ++ "nd";
          3 -> integer_to_list(N) ++ "rd";
          _ -> integer_to_list(N) ++ "th"
      end
     ).
