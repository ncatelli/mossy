# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Grammar

```
program: global_declaration*
        ;

global_declaration: function_declaration
        | var_declaration
        ;

function_declaration: type identifier '(' ')' compound_statement
        ;

compound_statement: '{' '}'
        |    '{' statement* '}'
        ;

statement: 
        | expression ';'
        | var_declaration
        | assignment
        | if_statement 
        | while_statement 
        | for_statement
        | return_stmt
        ;

var_declaration:   type identifier_list ';'
        ;

assignent:   identifier '=' expression ';'
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

expression: equality
        ;

equality: relational ( ( '==' | '!=' ) relational )*
        ;

relational: addition ( ( '<' | '<=' | '>' | '>=' ) addition )*
        ;

addition: multiplication ( ( '-' | '+' ) multiplication )* 
        ;

multiplication: call ( ( '/' | '*' ) call )* 
        ;

call: identifier '(' expression? ')'
        | prefix_expression
        ;

prefix_expression: '*' prefix_expression
        | '&' identifier
        | primary
        ;

primary: identifier
        | integer
        ;

char:   alphabetic
        ;


identifier_list: identifier
        | identifier ',' identifier_list
        ;

identifier: alphabetic+
        ;

type:   type_keyword optional_pointer
        ;

optional_pointer: ('*' optional_pointer)?
        ;

type_keyword: integer_type
        | 'void'
        ;


integer_type:
        'char'
        | 'short'
        | 'int'
        | 'long'
        ;


integer:  [0-9]*;

alphabetic: [a-zA-Z]+;
```