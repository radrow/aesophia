
-define(CONSTR(NS, Fun, Args, Body),
constr_expr(Env, {app, Ann, {typed, _, {qid, _, [NS, Fun]}, {fun_t, _, [], ArgsT, _}}, Args}, RetT, S0) ->
    Body;
    ).


-define(
   STDLIB_CONSTRS,
   ?CONSTR("List", "is_empty", [L],
           begin
               ExprT = fresh_liquid(Env, "is_empty", RetT),
               { ExprT
               , [ {well_formed, constr_id(), Env, ExprT}
                 , {subtype, constr_id(), Ann, Env,
                    refined(?bool_t(Ann), [?op(Ann, nu(Ann), '==', ?op(Ann, L, '==', ?int(Ann, 0)))]),
                    ExprT}
                 | S0
                 ]
               }
           end
          )

   %% ?CONSTR("List", "first", [L],
   %%         ({ refined(?bool_t(Ann), [?op(Ann, L, '==', 0)])
   %%          , [ {subtype, Ann, Env, }
   %%            | S0
   %%            ]
   %%          }
   %%         )
   %%        )
  ).
