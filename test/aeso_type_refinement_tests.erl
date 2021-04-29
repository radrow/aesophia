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
              ?assert(aeso_kurwamac:impl_holds(
                        maps:from_list([{"x", {id, [], "int"}}]), [], [{app, [], {'==', []}, [{id, [], "x"}, {id, [], "x"}]}]))
      end
      }
    ].

constraints_gen_test_() ->
    aeso_kurwamac:init_refiner(),
    [ {"Testing liquid template generation of " ++ ContractName,
       fun() ->
               try gen_constraints(ContractName) of
                   {ok, AST} ->
                       io:format("~p", [AST]), error(success);
                   {error, ErrBin} ->
                       io:format("\n~s", [ErrBin]),
                       error(ErrBin)
               catch _:T:S -> io:format("\n\n\n***** CHUJ 8===>\n stack:\n~p\n", [S]), error(T)
               end
           end} || ContractName <- compilable_contracts()].
gen_constraints(Name) ->
    io:format("no elo\n\n"),
    ContractString = aeso_test_utils:read_contract(Name),
    Ast = aeso_parser:string(ContractString, sets:new(), []),
    {_, _, TAst} = aeso_ast_infer_types:infer(Ast, [return_env]),
    [ begin
          {Con1, E, Cs} = aeso_kurwamac:constr_con(Con),
          Cs1 = aeso_kurwamac:simplify(Cs),
          Cs2 = aeso_kurwamac:group_subtypes(Cs1),
          Assg = aeso_kurwamac:solve(E, Cs2),
          [ io:format("~s : ~s\n", [Name, aeso_pretty:pp(dep_type, aeso_kurwamac:apply_assg(Assg, T))])
           || {Name, T} <- maps:to_list(element(2, E))
          ]
      end
     || Con <- TAst
    ],
    %% [ begin
    %%       {T, Cs} = aeso_kurwamac:constr_letfun(aeso_kurwamac:init_type_env(), Decl, []),
    %%       io:format("\n*** INFERRED\n\n~s\n\n",
    %%                 [prettypr:format(aeso_pretty:dep_type(T))
    %%                 ]),
    %%       Cs1 = aeso_kurwamac:simplify(Cs),
    %%       Cs2 = aeso_kurwamac:group_subtypes(Cs1),
    %%       io:format("**** CONSTRAINTS ****\n\n"),
    %%       [io:format("~s\n\n", [prettypr:format(aeso_pretty:constr(C))]) || C <- Cs],
    %%       Assg = aeso_kurwamac:solve(Cs2),
    %%       T1 = aeso_kurwamac:apply_assg(Assg, T),
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
