%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Sophia utility functions.
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_utils).

-export([scc/1, scc_group/2]).

-export_type([graph/1]).

%% -- Topological sort

-type graph(Node) :: #{Node => [Node]}. %% List of incoming edges (dependencies).

%% Topologically sorted strongly-connected components of a graph.
-spec scc(graph(Node)) -> [{cyclic, [Node]} | {acyclic, Node}].
scc(Graph) ->
    Trees = dfs(Graph, lists:reverse(postorder(dff(reverse_graph(Graph))))),
    Decode = fun(T) ->
        case postorder(T) of
            [I] -> case lists:member(I, maps:get(I, Graph, [])) of
                       true  -> {cyclic, [I]};
                       false -> {acyclic, I}
                   end;
            Is -> {cyclic, Is}
        end end,
    lists:map(Decode, Trees).

remove_dups([])    -> [];
remove_dups([H|T]) -> [H | [X || X <- remove_dups(T), X /= H]].
scc_group(Graph, Nodes) ->
    NodeVerts = fun({acyclic, N}) ->
                        maps:get(N, Graph, []);
                   ({cyclic, Ns}) -> remove_dups(lists:flatmap(fun (N) -> maps:get(N, Graph, []) end, Ns)) -- Ns
                end,
    SCCGraph = maps:from_list([{N, NodeVerts(N)} || N <- Nodes]),
    leaf_cutoff(SCCGraph, Nodes).

group_member(_, []) ->
    false;
group_member(X, [{acyclic, H}|T]) ->
    X == H orelse group_member(X, T);
group_member(X, [{cyclic, Hs}|T]) ->
    lists:member(X, Hs) orelse group_member(X, T).

leaf_cutoff(Graph, Nodes) ->
    leaf_cutoff(Graph, Nodes, [], []).
leaf_cutoff(_, [], Group, Acc) ->
    lists:reverse([Group|Acc]);
leaf_cutoff(Graph, [N|Rest], Group, Acc) ->
    Neigh = maps:get(N, Graph, []),
    case lists:any(fun(X) -> group_member(X, Group) end, Neigh) of
        false ->
            leaf_cutoff(Graph, Rest, [N|Group], Acc);
        true ->
            leaf_cutoff(Graph, Rest, [N], [Group|Acc])
    end.

%% Depth first spanning forest of a graph.
dff(Graph) ->
    dfs(Graph, maps:keys(Graph)).

dfs(Graph, Vs) ->
    {_, Trees} = dfs(Graph, #{}, Vs, []),
    Trees.

dfs(_Graph, Visited, [], Trees) -> {Visited, lists:reverse(Trees)};
dfs(Graph, Visited, [V | Vs], Trees) ->
    case maps:is_key(V, Visited) of
        true  -> dfs(Graph, Visited, Vs, Trees);
        false ->
            {Visited1, Tree} = dfs1(Graph, Visited#{ V => true }, V),
            dfs(Graph, Visited1, Vs, [Tree | Trees])
    end.

dfs1(Graph, Visited, V) ->
    Ws = maps:get(V, Graph, []),
    {Visited1, Trees} = dfs(Graph, Visited, Ws, []),
    {Visited1, {V, Trees}}.

%% Post-order traversal of a tree/forest.
postorder(Tree = {_, _}) -> postorder([Tree]);
postorder(Trees) when is_list(Trees) -> postorder(Trees, []).

postorder([], Acc) -> Acc;
postorder([{V, Trees1} | Trees], Acc) ->
    postorder(Trees1, [V | postorder(Trees, Acc)]).

from_edges(Is, Es) ->
    lists:foldl(fun({I, J}, G) ->
            maps:update_with(I, fun(Js) -> lists:umerge([J], Js) end, [J], G)
        end, maps:from_list([ {I, []} || I <- Is ]), Es).

reverse_graph(G) ->
    from_edges(maps:keys(G), [ {J, I} || {I, Js} <- maps:to_list(G), J <- Js ]).

