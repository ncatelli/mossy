# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Grammar
```

program: function_declaration*
        ;

function_declaration: 'void' identifier '(' ')' compound_statement
        ;

compound_statement: '{' '}'
        |    '{' statement* '}'
        ;

statement: 
        | expression ";"
        | declaration ";"
        | assignment ";"
        | if_statement 
        | while_statement 
        | for_statement
        ;

declaration:   'int' identifier
        ;

assignent:   identifier '=' expression 
        ;

if_statement: if_head
        | if_head 'else' compound_statement  ;

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


expression: equality
        ;

equality: relational ( ( "==" | "!=" ) relational )*
        ;

relational: addition ( ( "<" | "<=" | ">" | ">=" ) addition )*
        ;

addition: multiplication ( ( "-" | "+" ) multiplication )* 
        ;

multiplication: primary ( ( "/" | "*" ) primary )* 
        ;

primary: identifier
        | uint8
        ;

uint8:  [0-255]
        ;

identifier: alphabetic+
        ;

alphabetic: [a-zA-Z]+
```