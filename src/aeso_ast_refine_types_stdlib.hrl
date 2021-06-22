
-define(CONSTR(NS, Fun, Args, Body),
constr_expr(Env, {app, Ann, {typed, _, {qid, _, [NS, Fun]}, {fun_t, _, [], ArgsT, _}}, Args}, RetT, S0) ->
    Body;
    ).


-define(
   STDLIB_CONSTRS,
?CONSTR("List", "is_empty", [L],
        ({ refined(?bool_t(Ann), [?op(Ann, L, '==', 0)])
            , S0
            }
        )
       )
  ).
