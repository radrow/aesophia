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

%%  Very simply test compile the given contracts. Only basic checks
%%  are made on the output, just that it is a binary which indicates
%%  that the compilation worked.
%% template_gen_test_() ->
%%     [ {"Testing liquid template generation of " ++ ContractName,
%%        fun() ->
%%            case gen_templates(ContractName) of
%%                {ok, AST} ->
%%                    aeso_ast:pp(AST), error(xd);
%%                {error, ErrBin} ->
%%                    io:format("\n~s", [ErrBin]),
%%                    error(ErrBin)
%%            end
%%        end} || ContractName <- compilable_contracts()].

%% gen_templates(Name) ->
%%     ContractString = aeso_test_utils:read_contract(Name),
%%     Ast = aeso_parser:string(ContractString, sets:new(), []),
%%     {_, _, TAst} = aeso_ast_infer_types:infer(Ast, [return_env]),
%%     R = aeso_ast_refine_types:decorate_base_types(TAst),
%%     {ok, R}.

constraints_gen_test_() ->
        [ {"Testing liquid template generation of " ++ ContractName,
           fun() ->
               case gen_constraints(ContractName) of
                   {ok, AST} ->
                       io:format("~p", [AST]), error(xd);
                   {error, ErrBin} ->
                       io:format("\n~s", [ErrBin]),
                       error(ErrBin)
               end
           end} || ContractName <- compilable_contracts()].
gen_constraints(Name) ->
    ContractString = aeso_test_utils:read_contract(Name),
    Ast = aeso_parser:string(ContractString, sets:new(), []),
    {_, _, TAst} = aeso_ast_infer_types:infer(Ast, [return_env]),
    [ begin
          {T, Cs} = aeso_ast_refine_types:constr_letfun(aeso_ast_refine_types:init_env(), Decl, []),
          io:format("AA ~p", [T]),
          io:format("\n*** INFERRED\n\n~s\n\n",
                    [prettypr:format(aeso_pretty:dep_type(T))
                    ]
                   ),
          [io:format("~s\n\n", [prettypr:format(aeso_pretty:constr(C))]) || C <- Cs]
      end
      || {contract, _, _, Decls} <- TAst,
         Decl <- Decls,
        element(1, Decl) =:= letfun
    ],
    {ok, ok}.

%% compilable_contracts() -> [ContractName].
%%  The currently compilable contracts.
compilable_contracts() -> ["hagia"].
