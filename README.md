# mossy
A C-frontend built around cranelift.

## Grammar
```
expression: addition
          ;

addition: multiplication ( ( "-" | "+" ) multiplication )* 
          ;

multiplication: primary ( ( "/" | "*" ) primary )* 
        ;

primary: number 
        ;

number:  [0-9]*
        ;
```