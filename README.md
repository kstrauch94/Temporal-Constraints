# Temporal-Constraints
This module defines a theory and a propagator for temporal constraints. To write a temporal constraint use the form:
```
&constraint(min_time,max_time){<prefix>atom1(A1,...) ; <prefix>atom2(B1,...) ; ...} :- domain(A1), ... .
```
where <prefix> is one of ```+.```  ```+~```  ```-.```  ```-~``` 
  
After writing all constraints you have to define a signature theory atom for every theory term that appears in the theory constaint:
```
&signature{<prefix>atom1(A1,...)} :- domain(A1), ... .
```
where prefix is ```++``` or ```--``` depending on the prefix of the theory term that appears in the theory constraint.


# Installation

To install run the following command while in the main folder of the project:
pip install --editable .

# Run
To use this module use the "untimed" keyword. Use ```--help``` to see the available options.

```
untimed test-instances/hanoismall.lp encodings/hanoi-untimed-encoding.lp
```
