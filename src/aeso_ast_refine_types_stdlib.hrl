
-define(CONSTR(NS, Fun, Args, Body),
constr_expr(Env, {app, Ann, {typed, _, {qid, _, [NS, Fun]}, {fun_t, _, [], ArgsT, _}}, Args}, RetT, S0) ->
    Body;
    ).

-define(UNSOME(Pat, Constrs), [Pat] =
                   [ ArgT
                     || C <- Constrs,
                        ArgT <- case C of
                                    {dep_constr_t, CAnn, Con = {con, _, "Some"}, [CT]} -> [CT];
                                    _ -> []
                                end
                   ]).

-define(
   STDLIB_CONSTRS,
   ?CONSTR("List", "is_empty", [L],
           begin
               {_, S1} = constr_expr(Env, L, S0),
               ExprT = fresh_liquid(Env, "is_empty", RetT),
               { ExprT
               , [ {well_formed, constr_id(), Env, ExprT}
                 , {subtype, constr_id(), Ann, Env,
                    refined(?bool_t(Ann), [?op(Ann, nu(Ann), '==', ?op(Ann, L, '==', ?int(Ann, 0)))]),
                    ExprT}
                 | S1
                 ]
               }
           end
          )

    ?CONSTR("List", "first", [L],
           begin
               {{dep_list_t, _, _, ElemT, _}, S1} = constr_expr(Env, L, S0),
               ExprT = {dep_variant_t, _, Id, _, _, Constrs} = fresh_liquid(Env, "first", RetT),
               ?UNSOME(RetConT, Constrs),
               EnvEmpty = assert(?op(Ann, L, '==', ?int(Ann, 0)), Env),
               EnvCons = assert(?op(Ann, L, '>', ?int(Ann, 0)), Env),
               { ExprT
               , [ {well_formed, constr_id(), Env, ExprT}
                 , {subtype, constr_id(), Ann, EnvEmpty,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["None"]}, []}], Constrs},
                    ExprT}
                 , {subtype, constr_id(), Ann, EnvCons,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["Some"]}, [RetConT]}], Constrs},
                    ExprT}
                 , {subtype, constr_id(), Ann, EnvCons, ElemT, RetConT}
                 | S1
                 ]
               }
           end
           )

    ?CONSTR("List", "tail", [L],
           begin
               {{dep_list_t, _, _, ElemT, _}, S1} = constr_expr(Env, L, S0),
               ExprT = {dep_variant_t, _, Id, _, _, Constrs} = fresh_liquid(Env, "tail", RetT),
               ?UNSOME(RetConT, Constrs),
               EnvEmpty = assert(?op(Ann, L, '==', ?int(Ann, 0)), Env),
               EnvCons = assert(?op(Ann, L, '>', ?int(Ann, 0)), Env),
               LId = fresh_id(Ann, "tail_l"),
               { ExprT
               , [ {well_formed, constr_id(), Env, ExprT}
                 , {subtype, constr_id(), Ann, EnvEmpty,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["None"]}, []}], Constrs},
                    ExprT}
                 , {subtype, constr_id(), Ann, EnvCons,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["Some"]}, [RetConT]}], Constrs},
                    ExprT}
                 , {subtype, constr_id(), Ann, EnvCons,
                   {dep_list_t, Ann, LId, ElemT, [?op(Ann, LId, '==', ?op(Ann, L, '-', ?int(Ann, 1)))]}, RetConT}
                 | S1
                 ]
               }
           end
           )

    ?CONSTR("List", "last", [L],
           begin
               {{dep_list_t, _, _, ElemT, _}, S1} = constr_expr(Env, L, S0),
               ExprT = {dep_variant_t, _, Id, _, _, Constrs} = fresh_liquid(Env, "last", RetT),
               ?UNSOME(RetConT, Constrs),
               EnvEmpty = assert(?op(Ann, L, '==', ?int(Ann, 0)), Env),
               EnvCons = assert(?op(Ann, L, '>', ?int(Ann, 0)), Env),
               { ExprT
               , [ {well_formed, constr_id(), Env, ExprT}
                 , {subtype, constr_id(), Ann, EnvEmpty,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["None"]}, []}], Constrs},
                    ExprT}
                 , {subtype, constr_id(), Ann, EnvCons,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["Some"]}, [RetConT]}], Constrs},
                    ExprT}
                 , {subtype, constr_id(), Ann, EnvCons, ElemT, RetConT}
                 | S1
                 ]
               }
           end
           )

    ?CONSTR("List", "find_indices", [P, L], %% TODO: len == 0 if no way to fulfill
           begin
               {_, S1} = constr_expr(Env, P, S0),
               {_, S2} = constr_expr(Env, L, S1),
               ExprT = {dep_list_t, _, _, ElemT, _} = fresh_liquid(Env, "find_indices", RetT),
               LId = fresh_id(Ann, "find_indices_l"),
               { ExprT
               , [ {well_formed, constr_id(), Env, ExprT}
                 , {subtype, constr_id(), Ann,
                    {dep_list_t, Ann, LId, ElemT, [?op(Ann, LId, '=<', L)]},
                    ExprT
                   }
                 , {subtype, constr_id(), Env, ?d_nonneg_int(Ann), ElemT}
                 | S2
                 ]
               }
           end
           )

  ).
