# mossy
An (irresponsibly) experimental C compiler for the first-principles of computing project.

## Grammar
```

statements: statement*
        |   'int' identifier ';'
        |   identifier '=' expression ';'`
        ;

statement: expression ";"
        ;

expression: addition
        ;

addition: multiplication ( ( "-" | "+" ) multiplication )* 
        ;

multiplication: relational ( ( "/" | "*" ) relational )* 
        ;

relational: equality ( ( "<" | "<=" | ">" | ">=" ) equality )*
        ;

equality: primary ( ( "==" | "!=" ) primary )*
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