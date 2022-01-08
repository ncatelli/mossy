# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Grammar
Grammar is heavily referenced from [WMU cs4850 course grammar](https://cs.wmich.edu/%7Egupta/teaching/cs4850/sumII06/The%20syntax%20of%20C%20in%20Backus-Naur%20form.htm)

```
tranlation_unit: external_declaration*
        ;

external_declaration: function_declaration
        | var_declaration
        ;

function_declaration: type_declarator identifier '(' ')' compound_statement
        ;

compound_statement: '{' '}'
        |    '{' statement* '}'
        ;

statement: 
        | expression ';'
        | var_declaration
        | if_statement 
        | while_statement 
        | for_statement
        | return_stmt
        ;

var_declaration: type_declarator  '[' digit ']' ';'
        | type_declarator identifier_list ';'
        ;

if_statement: if_head
        | if_head 'else' compound_statement 
        ;

if_head: 'if' '(' expression ')' compound_statement 
        ;

while_statement: 'while' '(' expression ')' compound_statement
        ;

for_statement: 'for' '(' preop_statement ';'
                          expression ';'
                          postop_statement ')' compound_statement  ;

preop_statement: assignment 
        ;

postop_statement: expression
        ;

return_statement: 'return' expression? ';'
        ;

expression: assignment
        ;

assignment:   identifier '=' assignment
        | equality
        ;

equality: relational ( ( '==' | '!=' ) relational )*
        ;

relational: addition ( ( '<' | '<=' | '>' | '>=' ) addition )*
        ;

addition: multiplication ( ( '-' | '+' ) multiplication )* 
        ;

multiplication: call ( ( '/' | '%' | '*' ) call )* 
        ;

call: identifier '(' expression? ')'
        | prefix_expression
        ;

prefix_expression: '*' prefix_expression
        | '&' identifier
        | '++' prefix_expression
        | '--' prefix_expression
        | '!' prefix_expression
        | '-' prefix_expression
        | '~' prefix_expression
        | postfix_expression
        ;

postfix_expression: postfix_expression '[' expression ']'
        |
        ;

primary: identifier
        | string_literal
        | digit
        | grouping 
        ;

char:   ascii_alphabetic
        ;

grouping: '(' expression ')'
        ;

identifier_list: identifier
        | identifier ',' identifier_list
        ;

identifier: ( ascii_alphabetic | numeric | '_' )+
        ;

type_declarator:   type_specifier optional_pointer
        ;

optional_pointer: ('*' optional_pointer)?
        ;

type_specifier: 'char'
        | 'short int'
        | 'short'
        | 'int'
        | 'long long int'
        | 'long long'
        | 'long int'
        | 'long'
        | 'void'
        ;

string_literal: '"' ( ascii_alphanumeric | ' ' | ascii_whitespace | ascii_control | '\"')* '"'

digit:  [0-9]*;

ascii_alphabetic: [a-zA-Z]+;

ascii_alphanumeric: ascii_alphabetic
        | digit
        ;

ascii_whitespace: *DEVNOTE: ascii check spec*
        ;

ascii_control: *DEVNOTE: ascii check spec*
        ;

space: ' '
```