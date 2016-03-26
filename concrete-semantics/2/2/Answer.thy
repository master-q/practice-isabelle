(*
Exercise 2.2. Start from the definition of add given above. Prove that add
is associative and commutative. Define a recursive function double :: nat \<Rightarrow>
nat and prove double m = add m m.
*)

theory Answer
imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02 [simp]: "add m 0 = m"
apply(induction m)
apply(auto)
done

lemma add_03 [simp]: "add m (Suc n) = Suc (add m n)"
apply(induction m)
apply(auto)
done

lemma add_assoc: "add a (add b c) = add (add a b) c"
apply(induction a)
apply(auto)
done

lemma add_comm: "add m n = add n m"
apply(induction m)
apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = 2 + double n"

lemma double_add: "double m = add m m"
apply(induction m)
apply(auto)
done

end
