theory isabelle_problems

imports Complex_Main

begin

lemma test:
  fixes x y u b :: real
  assumes "0 < x" and "x < y" and "u < v"
  shows "2 * u + exp (1 + x + x^4) <= 2 * v + exp (1 + y + y^4)"

using assms apply -
by (metis add_less_cancel_left add_mono_thms_linordered_field(5) exp_less_cancel_iff less_eq_real_def mult_2 power_strict_mono zero_less_numeral)

lemma test2:
  fixes x y u b :: real
  assumes "0 < x" and "x < y" and "u < v"
  shows "2 * u + exp (1 + x + x^4) <= 2 * v + exp (1 + 2 * y + y^4)"

using assms apply -
by (smt exp_le_cancel_iff power_less_imp_less_base)

lemma test3: "(0::real) < x \<Longrightarrow> x < 1 ==> 1 / (1 - x) > 1 / (1 - x^2)"
(* sledgehammer times out *)
sorry 

lemma test4: "(0::real) \<le> n \<Longrightarrow> n \<le> (K / 2) * x \<Longrightarrow> 0 < C \<Longrightarrow> 0 < eps \<Longrightarrow> eps < 1 \<Longrightarrow> 
    (1 + eps / (3 * (C + 3))) * n < K * x"

  sorry

lemma test5: "(\<forall>x. f x \<le> 1) \<Longrightarrow> (0::real) < W \<Longrightarrow> u < v \<Longrightarrow> u + w * f x < v + w"
  sledgehammer  
  
(*
  apply (rule add_mono)
  apply auto
  apply (rule add_mono)
  apply arith
*)