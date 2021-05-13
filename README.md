# mossy
A C-frontend built around cranelift.

## Grammar
```

statements: statement
        | statement statements

statement: print" expression ";"
        ;

expression: addition
        ;

addition: multiplication ( ( "-" | "+" ) multiplication )* 
        ;

multiplication: primary ( ( "/" | "*" ) primary )* 
        ;

primary: uint8
        ;

uint8:  [0-255]
        ;
```