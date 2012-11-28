#!/usr/bin/python
import re
from collections import deque
import string

operator_dictionary = {}

class PToken:
    '''Token class used to represent each meaningful set of characters when a string is broken up into parts that must be parsed.'''
    def __init__(self, non_term, val, loc):
        self.non_term = non_term
        self.val = val
        self.loc = loc

    
class LexNode:
    '''A node for the parse tree that is generated to determine the truth of well-formed propositions.'''
    def __init__(self, token, parent = None):
        self.non_term = token.non_term
        self.val = token.val
        self.loc = token.loc
        self.parent = parent
        self.children = []

    def __str__(self):
        return "Non Terminal: %s\nValue: %s\n" % (self.non_term,self.val)


    def construct_text_from_nodes(self):
        '''Returns a string constructed by taking a preorder walk of the tree
and concatenating the values at each node. 

    Keyword Arguments:
    None

    Returns:
    A list of characters representating of the lex_tree starting at the node which originally called construct_text_from_nodes. Should be called with join()'''
        my_val = []
        if self.non_term != 'start':
            my_val = [self.val]

        for child in self.children:
            my_val += child.construct_text_from_nodes()
        return my_val
        
    def get_var_terms(self):
        '''A function which performs a preorder walk of the LexNode tree and returns the FOL constants, variables, and functions in the order they are found.

    Keyword Arguments:
    None

    Returns:
    A list of strings which are the values of the FOL constants, variables, and functions found in the tree.'''

        my_value = []
        if self.non_term in ['const','function','variable']:
            my_value = ['(' + self.val + ')']
        for child in self.children:
            my_value += child.get_var_terms()

        return my_value

class StripsOp:
    '''Node representing a STRIPS operator which contains its label, its parameters, its preconditions, add list, and delete list'''

    def __init__(self, label, parameters, list_of_changes):
        self.label = label
        self.parameters = parameters
        self.preconditions = list_of_changes[0]
        self.addList = list_of_changes[1]
        self.deleteList = list_of_changes[2]

    def __str__(self):
        return "Action: %s\nParameters: %s\nPreconditions: %s\nAdd List: %s\nDelete List: %s" % (self.label,self.parameters,self.preconditions,self.addList,self.deleteList)

    def execute_op(self, action_s, world_state):
        '''This function takes a string containing the strips operator and a list of strings representing the world state. Then, it changes the world_state list according to its add and delete list. 

    Keyword Arguments:
    action_s -- A string containing the STRIPS operator and its associated parameters
    world_state -- A list of strings containing the facts about the world at that moment.

    Returns:
    An updated world_state list.'''
    
        #We start with the full string. We're only interested in the variables passed to it.
        #Called (Add (|y|)(|x|)(|z|)) with addList '(P |x| |y|)'
        #       (Add (|b|)(|a|)(|c|))
        #param_list = ['|b|','|a|']
        param_list = get_exps(action_s[1:-1])
        #addList = '(P |x| |y|)'
        addList = '(' + " ".join(self.addList.construct_text_from_nodes()) + ')'
        add_vars = self.addList.get_var_terms()
        new_add_term = addList
        #add_vars = ['|x|','|y|']
        for variable in add_vars:
            #replace_index = ['(|y|)','(|x|),'(|z|)'].index('|x|')
            #replace_index = 1
            replace_index = self.parameters.index(variable)
            new_add_term = re.sub("\\" + self.parameters[replace_index][1:-2] + "\|", param_list[replace_index][1:-1], new_add_term)
        #Add the term from the add list
        world_state.append(new_add_term)

        subtract_vars = self.deleteList.get_var_terms()
        new_sub_term = '(' + " ".join(self.deleteList.construct_text_from_nodes()) + ')'
        for variable in subtract_vars:
            #replace_index = ['(|y|)','(|x|),'(|z|)'].index('|x|')
            #replace_index = 1
            replace_index = self.parameters.index(variable)
            new_sub_term = re.sub("\\" + self.parameters[replace_index][1:-2] + "\|", param_list[replace_index][1:-1], new_sub_term)

        sub_index = world_state.index(new_sub_term)
        #Splice out the term from the remove list. 
        world_state = world_state[:sub_index] + world_state[sub_index+1:]

        return world_state   

def tokenize_string(string):
    '''Takes a lisp-readable input, converts the string into tokens, and returns a double-ended queue of the tokens in the order they were found in the string
    
    Keyword Arguments:
    string -- The lisp-readable input string

    Returns:
    A double-ended queue of PToken objects created by tokenize-ing the string. Returns None if the input string is not well formed (bad formatting)'''
    tokens = deque()
    exp = string
    i = 0

    #Compile regular expression objects to be used when tokenizing input
    #NOTE: In the original problem definition, |j| was not an acceptable input, but because I needed one extra constant for the planning portion, I made |j| acceptable. I hope this isn't a problem, but it was the only way I could think of to get one more constant
    left_paren = re.compile('\(')
    right_paren = re.compile('\)')
    binary_ops = re.compile('AND|OR|EQUIV|IMPLIES')
    quantifier = re.compile('ALL|EXISTS')
    const_term = re.compile('\|[a-ej]\|')
    func_term = re.compile('\|[f-h]\|')
    var_term = re.compile('\|[u-z]\|')
    unary_ops = re.compile('NOT')
    atoms = re.compile('[A-Z]\d*|"[\w ]+"')
    ws = re.compile('[\s]+')
    while(i < len(exp)):
        match_l = left_paren.match(exp, i)
        if match_l: #If left parenthesis was read
            tokens.append(PToken('lparen',match_l.group(0),match_l.start()))
            i = match_l.end()#New location to start search
            continue  #Match was found, start over at new location after the match

        match_r = right_paren.match(exp, i)
        if match_r: #If right parenthesis was read
            tokens.append(PToken('rparen',match_r.group(0),match_r.start()))
            i = match_r.end()
            continue

        match_bin = binary_ops.match(exp, i)
        if match_bin:#If a binary op was read
            tokens.append(PToken('binaryop',match_bin.group(0),match_bin.start()))
            i = match_bin.end()
            continue
        
        match_quant = quantifier.match(exp, i)
        if match_quant:#if a quantifier was read
            tokens.append(PToken('quantifier',match_quant.group(0),match_quant.start()))
            i = match_quant.end()
            continue

        match_const = const_term.match(exp, i)
        if match_const:#if a constant term was read
            tokens.append(PToken('const', match_const.group(0),match_const.start()))
            i = match_const.end()
            continue

        match_func = func_term.match(exp, i)
        if match_func:#if a function term was read
            tokens.append(PToken('function', match_func.group(0),match_func.start()))
            i = match_func.end()
            continue

        match_var = var_term.match(exp, i)
        if match_var:#if a variable term was read
            tokens.append(PToken('variable', match_var.group(0),match_var.start()))
            i = match_var.end()
            continue

        match_un = unary_ops.match(exp, i)
        if match_un:#If a unary op was read
            tokens.append(PToken('unaryop',match_un.group(0),match_un.start()))
            i = match_un.end()
            continue

        match_atom = atoms.match(exp, i)
        if match_atom:#If an atom is read
            tokens.append(PToken('atom', match_atom.group(0),match_atom.start()))
            i = match_atom.end()
            continue
        match_ws = ws.match(exp, i)
        if match_ws:#If whitespace was read (but not end of input)
            i = match_ws.end()
            continue

        #This return statement is only reached if tokenizing an input that is not well formed
        return None
    
    #The input is well formed, return the deque of tokens
    return tokens

def construct_parse_tree(tokenized_input, is_FOL_tree=False):
    '''A function that creates an abstract syntax tree from a deque of parser tokens.
By default it does not build an AST based on first order logic, but by passing True as an optional second argument, it will generate an AST based on FOL.

    Keyword Arguments:
    tokenized_input -- A deque of PToken objects that is used to generate the AST
    is_FOL_tree -- A boolean value, false by default. When is_FOL_tree is true, the result AST is based on FOL.

    Returns:
    A LexNode object representing the root of an AST or None if the proposition is not well-formed.'''
    current_node = LexNode(PToken('start', 'start', -1))
    while tokenized_input:#While set is not empty
        c_token = tokenized_input.popleft()
        if c_token.non_term == 'lparen':
            #When left parenthesis is read use the next token's value to create a new node

            c_token = tokenized_input.popleft()
            #If next char is a right parenthesis, nothing inside the parenthesis, proposition is not well-formed
            if c_token.non_term == 'rparen':
                return None
            #Check to make sure that if tree is not a FOL-tree that a lowercase letter is not mistakenly deemed well-formed.
            if not is_FOL_tree:
                if not isFOLProposition(c_token):
                    temp = LexNode(c_token, current_node)
                    current_node.children.append(temp)
                    current_node = temp
                else:
                    return None
            else:
                temp = LexNode(c_token, current_node)
                current_node.children.append(temp)
                current_node = temp

        elif c_token.non_term == 'rparen':
            #Current node is finished, go up one level in the tree
            current_node = current_node.parent
        elif isOperator(c_token) or c_token.non_term == 'atom':
            #The operator, if one exists, is always the first term grabbed after a left parenthesis.The same goes for the capital-letter atoms
            #If a binary or unary op is found outside the first position, proposition is not well formed
            return None
        #Token is not a parenthesis or atom. If this tree is using FOL, then continue adding tokens, otherwise not well-formed and return None
        elif is_FOL_tree:
            current_node.children.append(LexNode(c_token,current_node))
        else:
            return None
    #parent should be None, this is the start node. If it isn't, there are unbalanced parenthesis.
    if current_node.non_term == 'start':
        return current_node
    else:
        return None 

def wfp_checker(input_string):
    '''Takes a lisp-readable input and returns t if it is a well-formed proposition, and nil if it is not.

    Keyword Arguments:
    input_string -- The lisp-readable string representing a proposition

    Returns:
    t if the proposition is well formed. nil if the proposition is not well formed.'''

    tokens = tokenize_string(input_string)
    if tokens is None: #the list is None, and not well-formed
        return 'nil'
    else:
        abstract_tree = construct_parse_tree(tokens)
        if abstract_tree: #A tree was generated, input is well-formed
            return 't'
        else:
            return 'nil'

def isFOLProposition(token):
    '''Takes a token and tests its non_term field to determine whether or not it uses first order logic.

    Keyword Arguments:
    token -- The token to be checked

    Returns:
    A boolean value, true if the token is part of first order logic, false if it is not.'''
    
    return (token.non_term == 'quantifier') or (token.non_term == 'const') or (token.non_term == 'variable') or (token.non_term == 'function')

def isOperator(token):
    '''Takes a token and tests its non_term field to determine wheter or not it as a binary or unary operator.

    Keyword Arguments:
    tokens -- The token to be checked

    Returns:
    A boolean value, true if the token is an operator, false if it is not.'''
    return (token.non_term == 'unaryop') or (token.non_term == 'binary_op')


def evaluate_tree(abstract_tree, truth_vals):
    '''A function that is given an abstract syntax tree represented as a tree of LexNodes and a dictionary of truth values for the individual atoms,
then recurses to the leaves and propagates the truth values obtained by applying the functions specified at function nodes
to the values of their children. 

    Keyword Arguments:
    abstract_tree -- A LexNode that represents the root of the tree. This may be the root of the whole tree, or the root of a sub-tree. Individual atoms will simply return their truth value.
    truth_vals -- A dictionary that maps atom symbols to their truth values

    Returns:
    The overall truth value of a well-formed proposition based on the truth values supplied as a boolean value.'''

    #Base case of recursion, return truth value of the atom
    if (abstract_tree.non_term == 'atom'):
        return truth_vals[abstract_tree.val]
    #Binary-op case
    elif abstract_tree.non_term == 'binaryop':
        #AND operator
        if abstract_tree.val == 'AND':
            return (evaluate_tree(abstract_tree.children[0], truth_vals) and evaluate_tree(abstract_tree.children[1], truth_vals))
        #OR operator
        elif abstract_tree.val == 'OR':
            return (evaluate_tree(abstract_tree.children[0], truth_vals) or evaluate_tree(abstract_tree.children[1], truth_vals))
        #IMPLIES operator. a->b can also be interpreted as ((!a) or b)
        elif abstract_tree.val == 'IMPLIES':
            return (not(evaluate_tree(abstract_tree.children[0], truth_vals)) or evaluate_tree(abstract_tree.children[1], truth_vals))
        #EQUIV operator. True if a == b, false if a != b
        else:
            return evaluate_tree(abstract_tree.children[0], truth_vals) == evaluate_tree(abstract_tree.children[1], truth_vals)
    #Unary-op case
    elif abstract_tree.non_term == 'unaryop':
        return (not evaluate_tree(abstract_tree.children[0], truth_vals))
    #Start node case
    else:
        return evaluate_tree(abstract_tree.children[0], truth_vals)

def TruthValue(truth_val_s, wfp_s):
    '''Determines the truth value of a well-formed proposition when given strings representing the truth values of the individual atoms and the proposition to be evaluated.

    Keyword Arguments:
    truth_val_s -- A string of pairs in the form ((atom val)(atom val)...(atom val)). The atom must conform to the standards of a well-formed proposition. The val must be either t or nil.
    wfp_s -- A string representing a well-formed proposition.

    Returns: 
    True if the result of the evaluation is true, and false if the statement evaluates to false based on the truth values given.'''

    #Generates a list of strings containing the key value pairs for truth assignments
    truth_list = re.findall('\([\w\s]+\)', truth_val_s[1:-1])

    #Generates a dictionary of truth values mapped to their respective atoms
    truth_val_dict = {}
    for pair in truth_list:
        atom = re.search('\w+(?=\s)', pair).group(0)
        value = re.search('(?<=\s)\w+', pair).group(0)
        if value == 't':
            truth_val_dict[atom] = True
        else:
            truth_val_dict[atom] = False
    
    #Tokenize the proposition and turn it into a parse-able tree.
    tokenized_prop = tokenize_string(wfp_s)
    lex_tree = construct_parse_tree(tokenized_prop)
    
    #Parse the tree based on the given truth values and return the overall evaluation of the proposition. t if True and nil if False
    statement_value = evaluate_tree(lex_tree, truth_val_dict)
    #The statement evaluated to true
    if statement_value:
        return 't'
    else:
        return 'nil'

def IsTautology(wfp_s):
    '''Takes a string that is a well-formed proposition and evaluates it for all possible truth values to determine if it is a tautology (true under all circumstances) or not.
    
    Keyword Arguments:
    wfp_s -- A string that is a well-formed proposition.

    Returns:
    't' if the well-formed proposition is a tautology, or 'nil' if it is not a tautology'''

    tokenized_input = tokenize_string(wfp_s)

    #Creates a list of the atoms in the proposition with no duplicates
    symbol_list = []
    for token in tokenized_input:
        if token.non_term == 'atom' and (not token.val in symbol_list):
            symbol_list.append(token.val)

    lex_tree = construct_parse_tree(tokenized_input)

    #Dictionary for mapping truth value to atoms
    val_dict = {}
    for i in range(2 ** len(symbol_list)):
        for j in range(len(symbol_list)):
            #If the jth bit of i is a 1, set corresponding atom to true
            if ((i >> j) & 1) == 1:
                val_dict[symbol_list[j]] = True
            else:
                val_dict[symbol_list[j]] = False
        #Use newly generated dictionary to test truth value of statement
        #If the tree evaluation returns nil, statement is not a tautology. Immediately return nil
        if evaluate_tree(lex_tree, val_dict) == False:
            return 'nil'
    #Statement was true under all possible truth values and is a tautology.
    return 't'

def wfp_checkerFOL(input_s):
    '''Takes a string as input and determines whether it is a well-formed proposition using first order logic.
This is done by tokenizing the input then constructing an abstract syntax tree. If part of this process returns None, the proposition is not well formed.

    Keyword Arguments:
    input_s -- The input string to be checked for well formedness
    Returns:
    't' if the proposition is well-formed using first order logic, 'nil' if it is not well-formed.'''
    tokenized_input = tokenize_string(input_s)
    if tokenized_input:
        #token deque is not null, attempt to construct AST
        lex_tree = construct_parse_tree(tokenized_input, True)
        if lex_tree:
            #tree was properly generated, proposition is well-formed
            return 't'
        else:
            return 'nil'
    return 'nil'

def get_exps(string_to_parse):
    '''Parses the string passed to it using a stack. The stack pushes chars 
until it hits a right parenthesis, it then pops until it reads a left
parenthesis. If there are no left parenthesis in the stack once popping is 
finished, then the term was an expression, and that portion of the string is
sliced and appended to the final list of expressions.

    Keyword Arguments:
    string_to_parse -- A string that has lisp-readable portions. Said portions are sliced and added to a list containing all the valid expressions found in the string

    Returns:
    list_exps -- A list of strings containing all the valid lisp expressions found within the input string'''

    paren_stack = []
    list_exps = []
    start_i = 0
    end_i = 0
    for i in range(len(string_to_parse)):
        if not string_to_parse[i] in string.whitespace:
            if not '(' in paren_stack:
                start_i = i
            #Found a right parenthesis, pop until you get a left parenthesis. If the stack is now empty, the right parenthesis was the end of a term.The next term will begin 1 spot later
            if string_to_parse[i] == ')':
                top = paren_stack.pop()
                while(top != '(' and len(paren_stack) > 0):
                    top = paren_stack.pop()
                #if the stack has no left parenthesis in it, we've popped off a full term
                if not '(' in paren_stack:
                    end_i = i+1
                    list_exps.append(string_to_parse[start_i:end_i])
            #Not a right parenthesis or the beginning of a term. Append as usual.
            else:
                paren_stack.append(string_to_parse[i])
    return list_exps


def wf_op_check(input_s):
    '''Takes a string as input and determines whether it is a well-formed STRIPs-like operator. This is done by determining
whether the label for the operator satisfies its requirements, then determining whether its preconditions, add list, and delete
list are well-formed based on how they were defined in wfp_checkerFOL and wfp_checker.

    Keyword Arguments:
    input_s -- The input string to be checked for well-formedness.
    Returns:
    't' if the operator is well-formed, 'nil' if it is not.'''

    #A well-formed operator looks like this:
    #(Label (Param (var1)(var2)) (Precon (...the preconditions...)) (AddList (...things to add...)) (DelList (...things to delete...)))
    #A label is well-formed if it starts with a capital letter and is followed by any number of letters
    operator_match = re.match("\([A-Z][A-Za-z]+", input_s)
    operator_name = ''
    if not operator_match is None:
        #slice off first character because it includes parenthesis which is not actually part of the name
        operator_name = operator_match.group(0)[1:]

    else:
        return 'nil'

    #get parameters, preconditions, add list, and delete list IN THAT ORDER. If they are formatted wrong or out of order, return nil.
    list_of_props = get_exps(input_s[1:-1])
    if (list_of_props[0][1:6] != 'Param')or (list_of_props[1][1:7] != 'Precon') or (list_of_props[2][1:8] != 'AddList') or (list_of_props[3][1:8] != 'DelList'):
        return 'nil'
    #grab parameters separately, then makek the list of props just the remaining terms.
    param_list = get_exps(list_of_props[0][1:-1])
    list_of_props = list_of_props[1:]
    #list_of_changes, if all the propositions are well-formed, will contain the Preconditions, Add List, and Delete List as 
    #lex_nodes that point to the tree for each item
    list_of_changes = []
    for item in list_of_props:
        logical_prop = get_exps(item[1:-1])
        if wfp_checkerFOL(logical_prop[0]) == 'nil':
            return 'nil'
        else:
            tokenized_s = tokenize_string(logical_prop[0])
            lex_tree = construct_parse_tree(tokenized_s, True)
            list_of_changes.append(lex_tree)
        
    #The operator is well formed, create a StripsOp with it, add it to the dictionary and return t.
    new_op = StripsOp(operator_name, param_list, list_of_changes)
    operator_dictionary[operator_name] = new_op

    return 't'

def demonstrate_plan():
    '''Reads from a text file which is lisp-readable, initializes the start
and goal states, and shows a user defined plan. At each stage, from
initialization to start, the input is tested for well-formedness.

    Keyword Arguments:
    None

    Returns:
    None'''
#Predicates: P - On(x,y)
#            Q - At(x,y)
#            R - CanLeaveTogether(x,y)
#Constants:  |a| - cat
#            |b| - rat
#            |c| - grain
#            |d| - left
#            |e| - right
#            |j| - boat
#IMPORTANT - In the original program specs |j| wasn't an acceptable value for FOL. I changed this so I could have one more constant.
    input_file = ""
    with open("prog3_plan_demo.in") as f:
        input_file = f.read()

    parsed_file = get_exps(input_file)
    world_state = []
    goal_state = []

    init_is_wf = True
    goal_is_wf = True
    actions_are_wf = True
    #If either the initial state, the goal state, or the actions are not well-formed, the rest of the file is processed, but the plan is not walked through, only tested for well-formedness

    for expression in parsed_file:
        if expression[1:5] == 'init':
           print('Initialization states: ' + expression)
           print('Determining well-formedness of initialization states...')
           init_exps = get_exps(expression[1:-1])
           init_is_wf = are_exps_wf(init_exps, "Initialization")
           world_state = init_exps
           if init_is_wf:
               print('Initialization states are well-formed.\n')
   
        if expression[1:5] == 'goal':
            print('Goal states: ' + expression)
            print('Determining well-formedness of goal states...')
            goal_exps = get_exps(expression[1:-1])
            goal_is_wf = are_exps_wf(goal_exps, "Goal")
            goal_state = goal_exps
            if goal_is_wf:
                print('Goal states are well formed.\n')
 

        if expression[1:8] == 'actions':
            print('Determining well-formedness of STRIPS operators...')
            for action in get_exps(expression[1:-1]):
                if wf_op_check(action) == 'nil':
                    actions_are_wf = False
                    print(action)
                    print('\n')
                    print('Operators are not well-formed.\n')
            if(actions_are_wf):
                print('Operators are well-formed.\n')
                    

        if expression[1:5] == 'plan':
            if not (actions_are_wf or goal_is_wf or init_is_wf):
                print('Cannot run through the plan because either the goals, initializations, or actions are not well-formed.')
                break


            else:
                print('Starting at a state of: ' + ",".join(world_state) + ' \nand a goal state of: ' + ",".join(goal_state) + "\n")
                #Iterate through the actions in the plan, print them out
                #and show the world state after each consecutive iteration
                plan = get_exps(expression[1:-1])
                for action in plan:
                    print(action)
                    print('')
                    match = re.match('\(' + "(" + "|".join([key for key in operator_dictionary.keys()]) + ")", action)
                    op_name = match.group(0)[1:]
                    #Find the key to a matching operator in our dictionary of operators, then call execute_op on it. 
                    for key in operator_dictionary.keys():
                        if op_name == key:
                           strips_op = operator_dictionary[op_name]
                           world_state = strips_op.execute_op(action, world_state)
                    print('New world state: ' + ",".join(world_state) + "\n")

                reached_goal = True
                for goal in goal_state:
                    if not goal in world_state:
                        reached_goal = False
                        break  
                print("Did we reach the goal state?")
                print("World State: ")
                print(world_state)
                print("Goal state: ")
                print(goal_state)
                if(reached_goal):
                    print("Yes!")
                else:
                    print("No")

                    

def are_exps_wf(list_of_exps, exp_type_s):
    '''This function iterates over the list_of_exps and determines whether they are well-formed within the context of first order logic. If they are not, it prints to the console that they are not. This is similar to wfp_checkerFOL but is only meant to be used in demonstrate_plan to keep code readable

    Keyword Arguments:
    list_of_exps -- A list of strings to be evaluated for well-formedness
    exp_type_s -- A string which indicates what kind of expressions are being tested, e.g. goal expressions, initialization expressions.

    Returns:
    True if completed, False if something is not well-formed'''

    is_wf = True

    for expression in list_of_exps:
        #if any of the initialization expressions are not well-formed
        #break and print that statements aren't well-formed.
        if wfp_checkerFOL(expression) == 'nil':
            print(expression)
            print(exp_type_s + " statements are not well formed.")
            is_wf = False

    return is_wf
   
if __name__ == '__main__':
    demonstrate_plan()
