(*
Exercise 2.1. Use the value command to evaluate the following expressions:
"1 + (2::nat )", "1 + (2::int )", "1 − (2::nat )" and "1 − (2::int )".
*)

theory Answer
imports Main
begin

value "1 + (2::nat )"
value "1 + (2::int )"
value "1 - (2::nat )"
value "1 - (2::int )"

end
