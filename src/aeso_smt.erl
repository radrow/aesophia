-module(aeso_smt).

-compile([export_all]).

-include_lib("eunit/include/eunit.hrl").

-type formula() :: {var, string()}
                 | {int, integer()}
                 | {app, string(), [formula()]}
                   .
-type formulae() :: [formula()].

start_z3() ->
    PortOpts = [exit_status, {line,1000000}],
    Port = open_port({spawn, "z3 -in"}, PortOpts),
    put(z3_connection, Port),
    ok.

stop_z3() ->
    port_close(get(z3_connection)).

get_z3() ->
    Z3 = get(z3_connection),
    if Z3 =:= undefined -> throw(z3_disconnected);
       true -> ok
    end,
    Z3.

send_z3(Query) ->
    Z3 = get_z3(),
    QueryStr = pp_formula(Query),
    %% io:format("Z3> ~s\n", [QueryStr]),
    port_command(Z3, binary:list_to_bin(QueryStr ++ "\n")).

check_sat() ->
    send_z3({app, "check-sat", []}),
    receive
        {_, {data, {eol, Resp}}} ->
            case string:trim(Resp) of
                "sat" ->
                    true;
                "unsat" -> false;
                X -> {error, {bad_answer, X}}
            end
    after 5000 -> {error, timeout}
    end.

assert(Form) ->
    send_z3({app, "assert", [Form]}).

declare_const(Var, Type) ->
    send_z3({app, "declare-const", [Var, Type]}).

push() ->
    send_z3({app, "push", []}).
pop() ->
    send_z3({app, "pop", []}).
scoped(Fun) ->
    push(),
    R = Fun(),
    pop(),
    R.


pp_formula({var, Name}) -> Name;
pp_formula({int, I}) -> integer_to_list(I);
pp_formula({app, Fun, Args}) ->
    io_lib:format("(~s)", [pp_formulae([{var, Fun}|Args])]).

pp_formulae([]) ->
    "";
pp_formulae([H]) ->
    pp_formula(H);
pp_formulae([H|T]) ->
    io_lib:format("~s ~s", [pp_formula(H), pp_formulae(T)]).
