include "globals.mzn";

% maximal number of states 
int: n_states;
% maximal number of actions
int: n_actions = n_states - 1;

% how many blocks do we have?
int: n_blocks;
% how many places on the table
int: n_places;

% set of the states' indices
set of int: States = 1..n_states;
set of int: Actions = 1..n_actions;

% set of the blocks' indices
set of int: Blocks = 1..n_blocks;
% set of places' indices
set of int: Places = -(n_places-1)..0;

% set of all the elements we have
set of int: Objects = Places union Blocks;

% initial blocks' locations
array[Blocks] of Objects: init_on;
% final blocks' locations
array[Blocks] of Objects: final_on;


% blocks' positions in various moments
array[States, Blocks] of var Objects: on;
% what block do we move at the given time
array[Actions] of var Blocks: what_we_move;
% where we move the block at the given time
array[Actions] of var Objects: where_to;
% time we reach the correct state
var States: end; 

% TODO: 
% 1. we have to set up initial locations
% 2. we have to set up final locations
% 3. block cannot lie on itself
% 4. no two blocks can lie on the same object
% 5. define predicate clear: 
% - an object `o` is clear at the time `s`, when there is nothing on it
%
%   predicate clear(States: s, var Objects: o) =
%     ...?
% 6. to the block `b` at the time 's', it has to be clear!
% 7. we can move the block only on the other clear positions
% 8. if the block at time `s+1` is somewhere as than at time `s`, it means:
% - we had do move it at the time `s`
% - the new position was the target poistion of the action at the `s`
% 9. after the `end` nothing should change!
% 10. the search strategy should start with smallest possible `end` and increase it step by step
%     - add the correct annotation
%   solve :: <missing search annotation> satisfy;

constraint forall(block in Blocks)(on[1,block]  = init_on[block]);

constraint forall(block in Blocks)(on[end,block]  = final_on[block]);

constraint forall(block in Blocks, state in States)(on[state,block]  != block);

constraint forall(block1, block2 in Blocks, state in States where block1 != block2)(on[state,block1]  != on[state,block2]);

predicate clear(States:s, var Objects: o) = not (o in row(on,s));

constraint forall(action in Actions)(clear(action,what_we_move[action]));
constraint forall(action in Actions)(clear(action,where_to[action]));

constraint forall(a in Actions, b in Blocks)(on[a,b] != on[a+1,b] -> (what_we_move[a] = b /\ where_to[a]=on[a+1,b]));

constraint forall(action in Actions)((action>=end) ->(row(on,action)=row(on,action+1)));

solve :: int_search([end], input_order, indomain_min, complete) satisfy;

% Don't mess with the output :)
output
    [ "[Finished after \(end-1) actions]\n" ] ++
    [ "State 1:\n" ] ++ [ "block \(b) on \(on[1, b])\n" | b in Blocks ] ++
    [ "-> [put \(what_we_move[s]) on \(where_to[s])]\n State \(s+1):\n" ++ 
      concat(["block \(b) on \(on[s+1, b])\n" | b in Blocks]) 
      | s in Actions where s + 1 <= fix(end)
    ];