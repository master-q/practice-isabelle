(*
Exercise 2.3. Define a function count :: 'a \<Rightarrow> 'a list \<Rightarrow> nat that counts the
number of occurrences of an element in a list. Prove count x xs \<le> length xs.
*)

theory Answer
imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count a [] = 0" |
"count a (x # xs) = (if a = x then 1 else 0) + count a xs"

lemma count_length: "count x xs \<le> length xs"
apply(induction xs)
apply(auto)
done

end
