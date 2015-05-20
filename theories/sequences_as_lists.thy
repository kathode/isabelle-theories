(******************************************************************************)
(* File: sequences_as_lists.thy                                               *)
(* Author: Pedro Ribeiro, University of York (UK)                             *)
(******************************************************************************)

header {* Simple encoding of sequences as lists *}

theory sequences_as_lists 
imports
  Main
  Sublist
  Order
begin

definition minusList :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "-\<^sub>t" 64)
where "minusList xs ys \<equiv> drop (length ys) xs" 

abbreviation prefixeqList :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infixr "\<le>\<^sub>t" 65)
where "(xs \<le>\<^sub>t ys) \<equiv> prefixeq xs ys"

abbreviation prefixList :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infixr "<\<^sub>t" 65)
where "(xs <\<^sub>t ys) \<equiv> prefix xs ys"

abbreviation concatList :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "^\<^sub>t" 65)
where "xs ^\<^sub>t ys \<equiv> xs @ ys"

abbreviation frontList :: "'a list  \<Rightarrow> 'a list" ("front'(_')\<^sub>t" 66)
where "frontList xs \<equiv> butlast xs"

abbreviation lastList :: "'a list  \<Rightarrow> 'a" ("last'(_')\<^sub>t" 67)
where "lastList xs \<equiv> last xs"

abbreviation headList :: "'a list \<Rightarrow> 'a" ("head'(_')\<^sub>t" 67)
where "headList xs \<equiv> hd xs"

abbreviation tailList :: "'a list \<Rightarrow> 'a list" ("tail'(_')\<^sub>t" 67)
where "tailList xs \<equiv> tl xs"

value "last([a,b])\<^sub>t"

text {* In HOL, the following is total, whereas in Z it wouldn't be.
        So care is needed to ensure that those functions are applied when
        satisfying the provisos of Z in order to obtain correct results.

        Furthermore, this is intended as an exercise, more than anything else.*}

value "last([])\<^sub>t"

text {* Similarly for front([]), where the result is [] rather than undefined. *}

value "front([])\<^sub>t" 

value "front(xs)\<^sub>t"

lemma list_minus_empty[simp]: "xs -\<^sub>t [] = xs"
  by (simp add:minusList_def)

lemma list_minus_extended[simp]: "(xs ^\<^sub>t ys) -\<^sub>t xs = ys"
  by (simp add:minusList_def)

lemma 
  assumes "xs \<le>\<^sub>t ys"
  shows "xs ^\<^sub>t (ys -\<^sub>t xs) = ys"
  apply (simp add:minusList_def)
  by (metis assms list_minus_extended minusList_def prefixeq_def)

lemma t_minus_s_cat_z__eq__t_cat_z_minus_s:
  assumes "s \<le>\<^sub>t t"
  shows "(t -\<^sub>t s) ^\<^sub>t z = (t ^\<^sub>t z) -\<^sub>t s"
  by (metis append_assoc assms list_minus_extended prefixeq_def)

lemma
  assumes "xs <\<^sub>t ys" and "xs \<noteq> []"
  shows "ys -\<^sub>t xs \<noteq> []"
  by (metis assms(1) list.distinct(1) list_minus_extended prefixE')

lemma
  assumes "xs <\<^sub>t ys"
  shows "ys -\<^sub>t xs \<noteq> []"
  by (metis assms list_minus_extended prefixE' prefix_bot.bot.not_eq_extremum prefix_simps(2))

lemma
  assumes "xs \<le>\<^sub>t ys" and "xs \<noteq> ys"
  shows "ys -\<^sub>t xs \<noteq> []"
  by (metis append_Nil2 assms(1) assms(2) list_minus_extended prefixeq_def)

lemma s_cat_t_empty__iff__s_empty_and_t_empty:
  shows "s ^\<^sub>t t = [] \<longleftrightarrow> s = [] \<and> t = []"
  by auto

lemma ys_not_empty:
  assumes "xs <\<^sub>t ys" and "xs \<noteq> []"
  shows "ys \<noteq> []"
  by (metis assms(1) prefix_simps(1))

lemma length_ys_gt_0:
  assumes "xs <\<^sub>t ys" and "xs \<noteq> []"
  shows "length ys > 0"
  by (metis assms(1) length_greater_0_conv prefix_simps(1))

lemma ys_not_empty_assms_front_xs_lt_ys__and__xs_not_empty:
  assumes "front(xs)\<^sub>t <\<^sub>t ys" and "xs \<noteq> []"
  shows "ys \<noteq> []"
  by (metis assms(1) prefix_simps(1))

lemma front_xs_ys__eq__xs_cat_front_ys:
  assumes "length ys > 0"
  shows "front(xs ^\<^sub>t ys)\<^sub>t = xs ^\<^sub>t front(ys)\<^sub>t"
  by (metis assms butlast_append length_greater_0_conv)

lemma front_xs_cat_ys__eq__front_xs:
  assumes "length ys = 0"
  shows "front(xs ^\<^sub>t ys)\<^sub>t = front(xs)\<^sub>t"
  by (metis append_Nil2 assms length_0_conv)

lemma front_element__eq__empty:
  shows "front([e])\<^sub>t = []"
  by (metis butlast.simps(2))

lemma last_element__eq__e:
  shows "last([e])\<^sub>t = e"
  by (metis last.simps)

lemma last_s_cat_t__eq__last_s:
  assumes "length t = 0"
  shows "last(s ^\<^sub>t t)\<^sub>t = last(s)\<^sub>t"
  by (metis append_Nil2 assms length_0_conv)
  
lemma last_s_cat_t__eq__last_t:
  assumes "length t > 0"
  shows "last(s ^\<^sub>t t)\<^sub>t = last(t)\<^sub>t"
  by (metis assms last_append length_greater_0_conv)

lemma length_tail_t_minus_front_s__gt__0:
  assumes "length s < length t" and "front(s)\<^sub>t <\<^sub>t t" and "length s > 0"
  shows "length(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) > 0"
  by (metis One_nat_def Suc_pred assms(1) assms(3) drop_Suc drop_eq_Nil length_0_conv length_butlast minusList_def neq0_conv not_less tl_drop)
  
lemma
  "(s \<le>\<^sub>t t \<and> (e ^\<^sub>t t) \<le>\<^sub>t u) \<longrightarrow> ((e ^\<^sub>t s) \<le>\<^sub>t u)"
  by (metis prefix_order.order_trans same_prefixeq_prefixeq)

lemma t_minus_front_s__eq__last_t:
  assumes "length t = length s" and "front(s)\<^sub>t <\<^sub>t t"
  shows "t -\<^sub>t front(s)\<^sub>t = [last(t)\<^sub>t]"  
  by (metis append_butlast_last_id assms(1) assms(2) length_butlast list_minus_extended minusList_def prefix_simps(1))

lemma sequence_strict_prefix:
  "s <\<^sub>t t \<longleftrightarrow> (\<exists>xs . s ^\<^sub>t xs = t \<and> (length xs) > 0)"
  by (metis length_0_conv neq0_conv prefix_def prefixeq_def self_append_conv)

lemma sequence_prefix:
  "s \<le>\<^sub>t t \<longleftrightarrow> (\<exists>xs . s ^\<^sub>t xs = t)"
  by (metis prefixeq_def)

lemma
  assumes "length s = length t" and "front(s)\<^sub>t <\<^sub>t t"
  shows "front(s)\<^sub>t <\<^sub>t t \<longleftrightarrow> front(s)\<^sub>t = front(t)\<^sub>t"
  by (metis append_Nil2 assms(1) assms(2) butlast_append length_butlast less_not_refl prefix_def prefixeq_def prefixeq_length_less)

lemma front_s_lt_t__and__front_z_lt_t__implies__front_s__eq__front_z:
  assumes "length s > 0" and "length z > 0"
  shows "length s = length z \<and> front(s)\<^sub>t <\<^sub>t t \<and> front(z)\<^sub>t <\<^sub>t t \<longrightarrow> front(s)\<^sub>t = front(z)\<^sub>t"
  apply (simp add:sequence_strict_prefix)
  apply (auto)
  done

text
{* This is an attempt at proving generic results about sequences of pairs. *}

type_synonym ('a, 'b) listPairs = "('a \<times> 'b) list"

text
{* This is an augmented construction about sequences of pairs, whose first
   element is also a sequence. *}

type_synonym ('a, 'b) listPairs_List = "('a list, 'b) listPairs"

value "head([1,2,4])\<^sub>t"

value "(fst(head([(1,2),(2,3)] -\<^sub>t front([(1,2),(2,3)])\<^sub>t)\<^sub>t),3)"

definition difA :: "('a, 'b) listPairs_List \<Rightarrow> ('a, 'b) listPairs_List  \<Rightarrow> ('a, 'b) listPairs_List" ("difA'(_,_')\<^sub>t" 67)
where "difA t s \<equiv> [(fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst(last(s)\<^sub>t),snd(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t))] ^\<^sub>t tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t"

definition FlatA :: "('a, 'b) listPairs_List \<Rightarrow> 'a list" ("FlatA'(_')\<^sub>t" 66)
where "FlatA tx \<equiv> concat (map fst tx)"

value "difA([([a,b],1)],[([a],1)])\<^sub>t"

value "FlatA([([1],2),([3,4],4)])\<^sub>t"

lemma s_prefix_t__implies__length_s_le_length_t:
  "s \<le>\<^sub>t t \<longrightarrow> length s \<le> length t"
  by (metis prefixeq_length_le)

lemma s_prefix_t__implies__not_length_t_le_length_s:
  "s \<le>\<^sub>t t \<longrightarrow> \<not> length t < length s"
  by (metis not_less prefixeq_length_le)

lemma length_s__eq__length_t__implies__s__eq__t:
  assumes "s \<le>\<^sub>t t" and "length t = length s"
  shows "s=t"
  by (metis assms(1) assms(2) not_equal_is_parallel parallel_def)

lemma last_tail_t_minus_front_s__eq__last_t:
  assumes "length s > 0"
  shows "front(s)\<^sub>t <\<^sub>t t \<and> length s < length t \<longrightarrow> last(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t = last(t)\<^sub>t"
  by (metis Nitpick.size_list_simp(2) assms drop_Suc last_drop length_butlast length_tl less_not_refl minusList_def tl_drop)

lemma tail_t_minus_front_s_not_empty:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "length t > length s"
  shows "tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t \<noteq> []"
  by (metis (mono_tags) One_nat_def Suc_pred assms(2) assms(3) drop_Suc drop_eq_Nil length_butlast minusList_def not_less tl_def tl_drop)

lemma tail_t_minus_front_s_empty:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "length t = length s"
  shows "tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t = []"
  by (metis assms(3) drop_eq_Nil length_butlast length_tl minusList_def order_refl tl_drop)

lemma last_difA_t_s__eq__last_t_one:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "length t > 0" and "length t > length s"
  shows "last(difA(t,s)\<^sub>t)\<^sub>t = last(t)\<^sub>t"
  apply (insert assms(1) assms(2) assms(4))
  apply (simp add:difA_def)
  by (metis One_nat_def Suc_pred assms(2) drop_Suc drop_eq_Nil last_drop length_butlast minusList_def not_less tl_drop)

lemma last_difA_t_s__eq__last_t_two:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "length t > 0" and "length t = length s"
  shows "last(difA(t,s)\<^sub>t)\<^sub>t = last(t)\<^sub>t"
  apply (insert assms(1) assms(2) assms(4))
  apply (simp add:difA_def)
  oops

lemma t_minus_front_s__eq__last_t_two:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "length t > 0" and "length t = length s"
  shows "t -\<^sub>t front(s)\<^sub>t = [last(t)\<^sub>t]"
  by (metis Ex_list_of_length Suc_pred add_Suc_right append_butlast_last_id assms(3) assms(4) length_0_conv length_butlast list.distinct(1) list.size(4) list_minus_extended minusList_def monoid_add_class.add.right_neutral)

lemma difA_length_t_eq_lengths__eq__fst:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "length t > 0" and "length t = length s"
  shows "difA(t,s)\<^sub>t = [(fst(last(t)\<^sub>t) -\<^sub>t fst(last(s)\<^sub>t),snd(last(t)\<^sub>t))]"
  apply (simp add:difA_def)
  by (metis (no_types, hide_lams) One_nat_def Suc_pred append_Nil2 assms(1) assms(3) assms(4) drop_Suc length_butlast list.sel(1) list.sel(3) list_minus_extended minusList_def prefixE' snoc_eq_iff_butlast tl_drop)

lemma snd_last_difA__eq__snd_last:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "length t > 0"
  shows "snd(last(difA(t,s)\<^sub>t)\<^sub>t) = snd(last(t)\<^sub>t)"
  apply (simp add:difA_def)
proof -
  have "length (front(s)\<^sub>t) < length t" using assms(1) prefixeq_length_less by blast
  thus "(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t = [] \<longrightarrow> snd (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) = snd (last(t)\<^sub>t)) \<and> (tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t \<noteq> [] \<longrightarrow> snd (last(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t) = snd (last(t)\<^sub>t))" by (metis (no_types) append_butlast_last_id drop_eq_Nil hd_append last_drop last_tl length_0_conv length_butlast length_tl list.sel(1) minusList_def not_less)
qed

lemma last_difA_t_s__eq__fst_last_t_minus_fst_last_s__snd_last_t:
  assumes "length t = length s" and "front(s)\<^sub>t <\<^sub>t t"
  shows "last(difA(t,s)\<^sub>t)\<^sub>t = (fst(last(t)\<^sub>t) -\<^sub>t fst(last(s)\<^sub>t),snd(last(t)\<^sub>t))"
  by (metis (erased, hide_lams) assms(1) assms(2) butlast.simps(1) difA_length_t_eq_lengths__eq__fst last.simps length_greater_0_conv prefix_order.less_irrefl)
  
lemma last_difA_t_s__eq__front_s_lt_t:
  assumes "length s < length t" and "front(s)\<^sub>t <\<^sub>t t"
  shows "last(difA(t,s)\<^sub>t)\<^sub>t = last(t)\<^sub>t"
  proof -
  have "last(difA(t,s)\<^sub>t)\<^sub>t
       =
       last([(fst (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(s)\<^sub>t),
           snd (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t))] ^\<^sub>t
         tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"
       by (simp only:difA_def)
  also have "... = last(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"
       oops

lemma t_cat_s__minus__t_cat_front_u__eq__s__minus__front_u:
  assumes "front(u)\<^sub>t \<le>\<^sub>t s"
  shows "(t ^\<^sub>t s) -\<^sub>t (t ^\<^sub>t front(u)\<^sub>t) = s -\<^sub>t front(u)\<^sub>t"
  by (metis append_assoc assms list_minus_extended prefixeq_def)

lemma difA_t_cat_s_t_cat_u__eq__difA_s_u:
  assumes "length u > 0" and "front(u)\<^sub>t \<le>\<^sub>t s"
  shows "difA(t ^\<^sub>t s, t ^\<^sub>t u)\<^sub>t = difA(s, u)\<^sub>t"
proof -
  have "difA(t ^\<^sub>t s, t ^\<^sub>t u)\<^sub>t = 
      [(fst (head(t ^\<^sub>t s -\<^sub>t front(t ^\<^sub>t u)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(t ^\<^sub>t u)\<^sub>t),
      snd (head(t ^\<^sub>t s -\<^sub>t front(t ^\<^sub>t u)\<^sub>t)\<^sub>t))] ^\<^sub>t
      tail(t ^\<^sub>t s -\<^sub>t front(t ^\<^sub>t u)\<^sub>t)\<^sub>t"
      by (simp only:difA_def)
  also have "... = [(fst (head((t ^\<^sub>t s) -\<^sub>t (t ^\<^sub>t front(u)\<^sub>t))\<^sub>t) -\<^sub>t fst (last(t ^\<^sub>t u)\<^sub>t),
      snd (head((t ^\<^sub>t s) -\<^sub>t (t ^\<^sub>t front(u)\<^sub>t))\<^sub>t))] ^\<^sub>t
      tail((t ^\<^sub>t s) -\<^sub>t (t ^\<^sub>t front(u)\<^sub>t))\<^sub>t"
      using assms(1)
      by (metis (erased, hide_lams) front_xs_ys__eq__xs_cat_front_ys)
  also have "... = [(fst (head((t ^\<^sub>t s) -\<^sub>t (t ^\<^sub>t front(u)\<^sub>t))\<^sub>t) -\<^sub>t fst (last(u)\<^sub>t),
      snd (head((t ^\<^sub>t s) -\<^sub>t (t ^\<^sub>t front(u)\<^sub>t))\<^sub>t))] ^\<^sub>t
      tail((t ^\<^sub>t s) -\<^sub>t (t ^\<^sub>t front(u)\<^sub>t))\<^sub>t"
      using assms(1)
      by (metis last_appendR length_greater_0_conv)
   also have "... = [(fst (head(s -\<^sub>t front(u)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(u)\<^sub>t),
      snd (head(s -\<^sub>t front(u)\<^sub>t)\<^sub>t))] ^\<^sub>t
      tail(s -\<^sub>t front(u)\<^sub>t)\<^sub>t"
      using assms(1) assms(2)
      by (metis t_cat_s__minus__t_cat_front_u__eq__s__minus__front_u)
   also have "... = difA(s, u)\<^sub>t"
      by (simp only:difA_def)
   finally show ?thesis .
qed

lemma difA_s_front_u_cat__fst_last_u__eq__difA_s_u:
  shows "difA(s, front(u)\<^sub>t ^\<^sub>t [(fst(last(u)\<^sub>t),r)])\<^sub>t = difA(s, u)\<^sub>t"
  by (metis butlast_snoc difA_def fst_conv last_snoc)

lemma difA_s_t__eq__difA_s_u:
  assumes "front(u)\<^sub>t = front(t)\<^sub>t" and "fst(last(t)\<^sub>t) = fst(last(u)\<^sub>t)"
  shows "difA(s,t)\<^sub>t = difA(s,u)\<^sub>t"
  by (metis assms(1) assms(2) difA_def)

lemma difA_difA_t_s_empty_snd_last_s__eq__difA_t_s:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0"
  shows "difA(difA(t,s)\<^sub>t,[([],snd(last(s)\<^sub>t))])\<^sub>t = difA(t,s)\<^sub>t"
proof -
  have "difA(difA(t,s)\<^sub>t,[([],snd(last(s)\<^sub>t))])\<^sub>t
        =
        [(fst(head(difA(t,s)\<^sub>t -\<^sub>t front([([],snd(last(s)\<^sub>t))])\<^sub>t)\<^sub>t)
           -\<^sub>t
           fst(last([([],snd(last(s)\<^sub>t))])\<^sub>t),
           snd(head(difA(t,s)\<^sub>t -\<^sub>t front([([],snd(last(s)\<^sub>t))])\<^sub>t)\<^sub>t))]
        ^\<^sub>t
        tail(difA(t,s)\<^sub>t -\<^sub>t front([([],snd(last(s)\<^sub>t))])\<^sub>t)\<^sub>t"
        by (simp only:difA_def)
   also have "... = [(fst(head(difA(t,s)\<^sub>t -\<^sub>t [])\<^sub>t)
           -\<^sub>t
           fst(last([([],snd(last(s)\<^sub>t))])\<^sub>t),
           snd(head(difA(t,s)\<^sub>t -\<^sub>t [])\<^sub>t))]
        ^\<^sub>t
        tail(difA(t,s)\<^sub>t -\<^sub>t [])\<^sub>t"
        by (metis front_element__eq__empty)
   also have "... = [(fst(head(difA(t,s)\<^sub>t -\<^sub>t [])\<^sub>t)
           -\<^sub>t
           fst(([],snd(last(s)\<^sub>t))),
           snd(head(difA(t,s)\<^sub>t -\<^sub>t [])\<^sub>t))]
        ^\<^sub>t
        tail(difA(t,s)\<^sub>t -\<^sub>t [])\<^sub>t"
        by (metis last_element__eq__e)
   also have "... = 
        [(fst(head(difA(t,s)\<^sub>t)\<^sub>t) -\<^sub>t fst(([],snd(last(s)\<^sub>t))),
        snd(head(difA(t,s)\<^sub>t)\<^sub>t))]
        ^\<^sub>t
        tail(difA(t,s)\<^sub>t)\<^sub>t"
        by (metis list_minus_empty)
   also have "... = 
        [(fst(head(difA(t,s)\<^sub>t)\<^sub>t),snd(head(difA(t,s)\<^sub>t)\<^sub>t))]
        ^\<^sub>t
        tail(difA(t,s)\<^sub>t)\<^sub>t"
        by (metis fst_conv list_minus_empty)
   also have "... = [head(difA(t,s)\<^sub>t)\<^sub>t] ^\<^sub>t tail(difA(t,s)\<^sub>t)\<^sub>t"
        by (metis prod.collapse)
   also have "... = difA(t,s)\<^sub>t"
        by (metis append_Cons append_Nil difA_def list.collapse list.distinct(1))

   finally show ?thesis .
qed

lemma
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0"
  shows "fst(head(difA(t,s)\<^sub>t)\<^sub>t) = fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst(last(s)\<^sub>t)"
  by (metis append_Cons difA_def fst_conv list.sel(1))

text
{* Results about Flat *}

lemma FlatA_s_cat_t__eq__Flat_s_cat_Flat_t:
  shows "FlatA(s ^\<^sub>t t)\<^sub>t = FlatA(s)\<^sub>t ^\<^sub>t FlatA(t)\<^sub>t"
  by (simp add:FlatA_def)

lemma FlatA_seq_s__eq__seq_s:
  shows "FlatA([([s],t)])\<^sub>t = [s]"
  by (simp add:FlatA_def)
  
lemma FlatA_s_non_empty__eq__fst_head_s_cat_FlatA_tail_s:
  assumes "length s > 0"
  shows "FlatA(s)\<^sub>t = fst(head(s)\<^sub>t) ^\<^sub>t FlatA(tail(s)\<^sub>t)\<^sub>t"
  by (metis FlatA_def assms concat.simps(2) length_greater_0_conv list.collapse list.simps(9))

lemma FlatA_s_non_empty__eq__FlatA_front_s_cat_fst_last_s:
  assumes "length s > 0"
  shows "FlatA(s)\<^sub>t = FlatA(front(s)\<^sub>t)\<^sub>t ^\<^sub>t fst(last(s)\<^sub>t)"
  by (metis FlatA_s_cat_t__eq__Flat_s_cat_Flat_t FlatA_s_non_empty__eq__fst_head_s_cat_FlatA_tail_s append_butlast_last_id assms butlast_snoc last_snoc less_numeral_extra(3) list.distinct(1) list.size(3) prefix_simps(2) prefixeq_length_less rotate1.simps(2) rotate1_hd_tl self_append_conv) 

lemma
  assumes "length s > 0" and "length t > 0" and "length z > 0"
  shows "FlatA(s)\<^sub>t = [] \<and> FlatA(z)\<^sub>t = [] \<and> length s = length z \<and> front(s)\<^sub>t <\<^sub>t t \<and> front(z)\<^sub>t <\<^sub>t t
         \<longrightarrow>
         fst(last(s)\<^sub>t) = fst(last(z)\<^sub>t) \<and> front(s)\<^sub>t = front(z)\<^sub>t"
  by (metis FlatA_s_non_empty__eq__FlatA_front_s_cat_fst_last_s append_is_Nil_conv assms(1) front_s_lt_t__and__front_z_lt_t__implies__front_s__eq__front_z)

lemma FlatA_head_s__eq__fst_head_s:
  assumes "length s > 0"
  shows "FlatA([head(s)\<^sub>t])\<^sub>t = fst(head(s)\<^sub>t)"
  by (simp add:FlatA_def)

lemma FlatA_last_s__eq__fst_last_s:
  assumes "length s > 0"
  shows "FlatA([last(s)\<^sub>t])\<^sub>t = fst(last(s)\<^sub>t)"
  by (simp add:FlatA_def)

lemma FlatA_t_minus_s__eq__FlatA_t_minus_FlatA_s:
  assumes "s \<le>\<^sub>t t"
  shows "FlatA(t -\<^sub>t s)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t"
  by (metis FlatA_s_cat_t__eq__Flat_s_cat_Flat_t assms list_minus_extended prefixeq_def)

lemma FlatA_t_minus_front_s__eq__FlatA_t_minus_FlatA_front_s:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "fst(last(s)\<^sub>t) \<le>\<^sub>t fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)"
  shows "FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t)\<^sub>t"
  by (metis FlatA_t_minus_s__eq__FlatA_t_minus_FlatA_s assms(1) prefix_def)

lemma FlatA_t_minus_s_minus_FlatA_z__eq__FlatA_t_minus_FlatA_s_cat_z:
  assumes "s \<le>\<^sub>t t" and "(s ^\<^sub>t z) \<le>\<^sub>t t"
  shows "FlatA(t-\<^sub>ts)\<^sub>t -\<^sub>t FlatA(z)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s ^\<^sub>t z)\<^sub>t"
  by (smt2 FlatA_s_cat_t__eq__Flat_s_cat_Flat_t FlatA_t_minus_s__eq__FlatA_t_minus_FlatA_s append_assoc assms(1) assms(2) list_minus_extended prefixeq_def)

lemma FlatA_t_minus_s_minus_FlatA_z__eq__FlatA_t_minus_FlatA_s_cat_z_lt:
  assumes "s <\<^sub>t t" and "(s ^\<^sub>t z) <\<^sub>t t"
  shows "FlatA(t-\<^sub>ts)\<^sub>t -\<^sub>t FlatA(z)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s ^\<^sub>t z)\<^sub>t"
  by (metis FlatA_t_minus_s_minus_FlatA_z__eq__FlatA_t_minus_FlatA_s_cat_z append_prefixeqD assms(2) prefix_order.less_imp_le)

lemma FlatA_t_minus_s_minus_FlatA_z__eq__FlatA_t_minus_FlatA_s_cat_z_le:
  assumes "s <\<^sub>t t" and "(s ^\<^sub>t z) \<le>\<^sub>t t"
  shows "FlatA(t-\<^sub>ts)\<^sub>t -\<^sub>t FlatA(z)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s ^\<^sub>t z)\<^sub>t"
  by (metis FlatA_t_minus_s_minus_FlatA_z__eq__FlatA_t_minus_FlatA_s_cat_z append_prefixeqD assms(2))

lemma
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "fst(last(s)\<^sub>t) \<le>\<^sub>t fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)"
  shows "FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t ^\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t"
  oops

lemma fst_last_s__le__fst_head_t_minus_front_s:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0"
  shows "fst(last(s)\<^sub>t) \<le>\<^sub>t fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)
         \<longrightarrow>
         FlatA([last(s)\<^sub>t])\<^sub>t \<le>\<^sub>t FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t"
  apply (simp add:FlatA_def)
  by (metis (erased, hide_lams) FlatA_def FlatA_s_non_empty__eq__fst_head_s_cat_FlatA_tail_s assms(1) list_minus_extended prefixeq_append sequence_strict_prefix)

lemma s_cat_t__minus__s_cat_z__eq__t_minus_z:
  assumes "z \<le>\<^sub>t t"
  shows "(s ^\<^sub>t t) -\<^sub>t (s ^\<^sub>t z) = t -\<^sub>t z"
  by (metis append_assoc assms list_minus_extended prefixeq_def)

lemma FlatA_t_minus_FlatA_s__eq__FlatA_t_minus_front_s__minus__FlatA_last_s:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "fst(last(s)\<^sub>t) \<le>\<^sub>t fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)"
  shows "FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t = FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t"
proof -
  have "FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t ^\<^sub>t [last(s)\<^sub>t])\<^sub>t"
    by (metis append_butlast_last_id assms(2) length_greater_0_conv)
  also have "... = FlatA(front(s)\<^sub>t ^\<^sub>t (t -\<^sub>t front(s)\<^sub>t))\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t ^\<^sub>t [last(s)\<^sub>t])\<^sub>t"
    by (metis assms(1) list_minus_extended prefixE')
  also have "... = (FlatA(front(s)\<^sub>t)\<^sub>t ^\<^sub>t FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t FlatA(front(s)\<^sub>t ^\<^sub>t [last(s)\<^sub>t])\<^sub>t"
    by (metis FlatA_s_cat_t__eq__Flat_s_cat_Flat_t)
  also have "... = (FlatA(front(s)\<^sub>t)\<^sub>t ^\<^sub>t FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t (FlatA(front(s)\<^sub>t)\<^sub>t ^\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t)"
    by (metis FlatA_s_cat_t__eq__Flat_s_cat_Flat_t)
  also have  "... = FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t"
    apply (insert assms(2))
    apply (insert assms(3))
    apply (insert s_cat_t__minus__s_cat_z__eq__t_minus_z 
          [where s="FlatA(front(s)\<^sub>t)\<^sub>t"
             and t="FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t"
             and z="FlatA([last(s)\<^sub>t])\<^sub>t"])
    by (metis FlatA_last_s__eq__fst_last_s FlatA_s_non_empty__eq__fst_head_s_cat_FlatA_tail_s assms(1) assms(2) drop_eq_Nil list.size(3) list_minus_empty minusList_def not_less prefixeq_append prefixeq_length_less)
    
  finally show ?thesis .
qed

lemma front_s_lt_t__implies__not_length_t_lt_length_s:
  assumes "length s > 0"
  shows "front(s)\<^sub>t <\<^sub>t t \<longrightarrow> \<not> (length t < length s)"
  by (smt2 Nitpick.size_list_simp(2) append_is_Nil_conv butlast_append drop_Suc drop_eq_Nil length_butlast length_tl not_less prefixeq_def prefixeq_length_le sequence_strict_prefix)

lemma not_lenth_s_lt_length_t__eq__length_s_eq_length_t:
  assumes "length s > 0" and "front(s)\<^sub>t <\<^sub>t t"
  shows "(\<not> (length s < length t)) = (length s = length t)"
proof -
  have "(\<not> (length s < length t)) = ((length t < length s) \<or> (length s = length t))"
      by (metis not_less_iff_gr_or_eq)
  also have "... = (length s = length t)"
      using assms
        (*   apply (insert assms(1))
           apply (insert assms(2))
           apply (insert front_s_lt_t__implies__not_length_t_lt_length_s
                  [where s=s and t=t]) *)
      by (simp add:front_s_lt_t__implies__not_length_t_lt_length_s)

  finally show ?thesis .
qed

lemma tail_t_minus_front_s_eq_lengths__eq__empty:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s = length t"
  shows "tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t = []"
  by (metis assms(1) assms(2) list.sel(3) t_minus_front_s__eq__last_t)

(* Sledgehammer previously suggested the following long and potentially non-terminating proof.

  proof -
  have f1: "\<And>x\<^sub>1 x\<^sub>2. drop (length (x\<^sub>1\<Colon>'a list)) (x\<^sub>1 ^\<^sub>t x\<^sub>2) = x\<^sub>2" by simp
  have f2: "Suc (length (front(s)\<^sub>t)) = length s" using assms by auto
  { assume "front(t)\<^sub>t \<noteq> front(s)\<^sub>t"
    moreover
    { assume "drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t"
      moreover
      { assume "drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t \<and> \<not> [] <\<^sub>t front(drop (length (front(s)\<^sub>t)) t)\<^sub>t"
        moreover
        { assume "drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t \<and> \<not> [] <\<^sub>t drop (length (front(s)\<^sub>t)) (front(t)\<^sub>t)"
          moreover
          { assume "drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t \<and> \<not> ([]\<Colon>'a list) <\<^sub>t esk1\<^sub>2 (front(s)\<^sub>t) (front(t)\<^sub>t)"
            hence "drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t \<and> \<not> 0 < length (esk1\<^sub>2 (front(s)\<^sub>t) (front(t)\<^sub>t))" using sequence_strict_prefix by blast
            hence "drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t \<and> \<not> front(s)\<^sub>t <\<^sub>t front(t)\<^sub>t" using sequence_strict_prefix by blast (* > 2 s, timed out *) }
          moreover
          { assume "esk1\<^sub>2 (front(s)\<^sub>t) (front(t)\<^sub>t) \<noteq> drop (length (front(s)\<^sub>t)) (front(t)\<^sub>t) \<and> drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t"
            hence "front(s)\<^sub>t ^\<^sub>t esk1\<^sub>2 (front(s)\<^sub>t) (front(t)\<^sub>t) \<noteq> front(t)\<^sub>t \<and> drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t" using f1 by metis
            hence "drop (length (front(s)\<^sub>t)) t \<noteq> [] \<and> front(t)\<^sub>t \<noteq> front(s)\<^sub>t \<and> \<not> front(s)\<^sub>t <\<^sub>t front(t)\<^sub>t" using sequence_strict_prefix by blast (* > 2 s, timed out *) }
          ultimately have "front(s)\<^sub>t ^\<^sub>t front(drop (length (front(s)\<^sub>t)) t)\<^sub>t \<noteq> front(t)\<^sub>t \<and> drop (length (front(s)\<^sub>t)) t \<noteq> []" by (metis prefix_def prefixeq_def) }
        ultimately have "front(s)\<^sub>t ^\<^sub>t front(drop (length (front(s)\<^sub>t)) t)\<^sub>t \<noteq> front(t)\<^sub>t \<and> drop (length (front(s)\<^sub>t)) t \<noteq> []" using f1 by metis }
      ultimately have "Suc (length (front(t)\<^sub>t)) = length t \<longrightarrow> (front(s)\<^sub>t <\<^sub>t t \<and> \<not> length s < length t \<longrightarrow> length s = length t) \<or> front(s)\<^sub>t ^\<^sub>t front(drop (length (front(s)\<^sub>t)) t)\<^sub>t \<noteq> front(t)\<^sub>t \<and> drop (length (front(s)\<^sub>t)) t \<noteq> []" using f1 f2 by (metis One_nat_def add_Suc_right append.simps(2) drop_eq_Nil list.size(4) monoid_add_class.add.right_neutral not_less prefix_def) }
    ultimately have "0 < length (drop (length (front(s)\<^sub>t)) t) \<and> Suc (length (front(t)\<^sub>t)) = length t \<longrightarrow> (front(s)\<^sub>t <\<^sub>t t \<and> \<not> length s < length t \<longrightarrow> length s = length t) \<or> front(s)\<^sub>t ^\<^sub>t front(drop (length (front(s)\<^sub>t)) t)\<^sub>t \<noteq> front(t)\<^sub>t \<and> drop (length (front(s)\<^sub>t)) t \<noteq> []" by blast }
  moreover
  { assume "\<not> 0 < length (drop (length (front(s)\<^sub>t)) t)"
    moreover
    { assume "\<not> 0 < length (esk1\<^sub>2 (front(s)\<^sub>t) t\<Colon>'a list)"
      hence "front(s)\<^sub>t <\<^sub>t t \<and> \<not> length s < length t \<longrightarrow> length s = length t" using sequence_strict_prefix by blast (* > 2 s, timed out *) }
    ultimately have "esk1\<^sub>2 (front(s)\<^sub>t) t = drop (length (front(s)\<^sub>t)) t \<longrightarrow> front(s)\<^sub>t <\<^sub>t t \<and> \<not> length s < length t \<longrightarrow> length s = length t" by presburger }
  moreover
  { assume "front(s)\<^sub>t ^\<^sub>t esk1\<^sub>2 (front(s)\<^sub>t) t \<noteq> t"
    hence "front(s)\<^sub>t <\<^sub>t t \<and> \<not> length s < length t \<longrightarrow> length s = length t" using sequence_strict_prefix by blast (* > 2 s, timed out *) }
  ultimately show "front(s)\<^sub>t <\<^sub>t t \<and> \<not> length s < length t \<longrightarrow> length s = length t" using f1 by (metis (no_types) Nitpick.size_list_simp(2) append_is_Nil_conv butlast_append length_butlast length_greater_0_conv length_tl)
qed*)
(*  by (metis Ex_list_of_length Nitpick.size_list_simp(2) One_nat_def Suc_pred add_Suc_right append.simps(1) append.simps(2) append_assoc append_eq_append_conv append_is_Nil_conv assms butlast.simps(1) butlast_append drop_eq_Nil length_butlast length_greater_0_conv length_tl list.distinct(1) list.size(3) list.size(4) list_minus_extended minusList_def monoid_add_class.add.right_neutral not_less prefixeq_def sequence_strict_prefix tl_def)
*)

lemma
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "length t > 0" and "fst(last(s)\<^sub>t) \<le>\<^sub>t fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)"
  shows "FlatA(t-\<^sub>tfront(s)\<^sub>t)\<^sub>t -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t ^\<^sub>t [last(s)\<^sub>t])\<^sub>t"
  apply (insert FlatA_t_minus_s__eq__FlatA_t_minus_FlatA_s
         [where s="front(s)\<^sub>t" and t=t])
  by (metis FlatA_last_s__eq__fst_last_s FlatA_s_cat_t__eq__Flat_s_cat_Flat_t FlatA_s_non_empty__eq__FlatA_front_s_cat_fst_last_s FlatA_t_minus_FlatA_s__eq__FlatA_t_minus_front_s__minus__FlatA_last_s assms(1) assms(2) assms(4))
(*  by (metis FlatA_t_minus_FlatA_s__eq__FlatA_t_minus_front_s__minus__FlatA_last_s append_butlast_last_id assms(1) assms(2) assms(4) less_nat_zero_code list.size(3)) *)

text {* Proof of Lemma 24. *}
lemma
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "fst(last(s)\<^sub>t) \<le>\<^sub>t fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)"
  shows "FlatA(difA(t,s)\<^sub>t)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t"
proof -
  (* Before splitting the cases, enforce that s cannot be smaller than t. *)
  have eq_lengths: "(\<not> length s < length t) = (length s = length t)"
      by (smt2 assms(1) assms(2) not_lenth_s_lt_length_t__eq__length_s_eq_length_t)

  then (* Now we split the cases. *)
  have thesis:"FlatA(difA(t,s)\<^sub>t)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t"
      apply (cases "length s < length t")
      apply auto
      proof -
  
  (* #s < #t *)
  show "length s < length t \<Longrightarrow> FlatA(difA(t,s)\<^sub>t)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t"
  proof -
    have "FlatA(difA(t,s)\<^sub>t)\<^sub>t = FlatA([(fst (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(s)\<^sub>t), snd (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t))] ^\<^sub>t
          tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"
          by (simp add:difA_def)
    also have "... = FlatA([(fst (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(s)\<^sub>t), snd (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t))])\<^sub>t ^\<^sub>t
          FlatA(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"
          by (metis FlatA_s_cat_t__eq__Flat_s_cat_Flat_t)
    also have "... = (fst (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(s)\<^sub>t)) ^\<^sub>t
          FlatA(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"
          by (simp add:FlatA_def)
    also have "... = (fst (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t) ^\<^sub>t
          FlatA(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"
          by (simp add:FlatA_def)
    also have "... = (FlatA([head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t])\<^sub>t -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t) ^\<^sub>t
          FlatA(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"
          by (simp add:FlatA_def)
    also have "... = (FlatA([head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t])\<^sub>t ^\<^sub>t
          FlatA(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t)"
          apply (insert assms(3))
          apply (insert t_minus_s_cat_z__eq__t_cat_z_minus_s 
                [where t="FlatA([head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t])\<^sub>t" 
                   and s="FlatA([last(s)\<^sub>t])\<^sub>t"
                   and z="FlatA(tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"])
          by (simp add:FlatA_def)
    also have "... = (FlatA([head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t] ^\<^sub>t
          tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t)"
          by (metis FlatA_s_cat_t__eq__Flat_s_cat_Flat_t)
    also have "... = (FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t)"
          by (metis append_Cons append_Nil append_Nil2 assms(1) calculation list.collapse list_minus_extended prefix_order.less_imp_le prefix_order.less_irrefl prefixeqE)
    also have "... = FlatA(t)\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t ^\<^sub>t [last(s)\<^sub>t])\<^sub>t"
          apply (insert assms(1))
          apply (insert assms(2))
          apply (insert assms(3))
          apply (insert FlatA_t_minus_FlatA_s__eq__FlatA_t_minus_front_s__minus__FlatA_last_s 
                [where s=s and t=t])
          by (simp_all)
    also have "... = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t"
         apply (insert assms(2))
         by (metis append_butlast_last_id less_numeral_extra(3) list.size(3))
    finally show ?thesis .
   qed

   (* #s = #t *)
   next    
     show "length s = length t \<Longrightarrow> FlatA(difA(t,s)\<^sub>t)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t"

     proof - (* In order to reference the assumption again, we create a label here. *)
     assume 0: "length s = length t"
     have "FlatA(difA(t,s)\<^sub>t)\<^sub>t = FlatA([(fst (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(s)\<^sub>t), snd (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t))] ^\<^sub>t
          tail(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)\<^sub>t"
          by (simp add:difA_def)
     also have "... = FlatA([(fst (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(s)\<^sub>t), snd (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t))])\<^sub>t"
          using assms and 0 (* Now can use the assumption above. *)
          by (simp add:tail_t_minus_front_s_eq_lengths__eq__empty)
     also have "... = fst (head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(s)\<^sub>t)"
          using assms and 0
          by (metis FlatA_head_s__eq__fst_head_s fst_conv length_greater_0_conv list.distinct(1) list.sel(1))
     also have "... = FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t -\<^sub>t fst(last(s)\<^sub>t)"
          using assms and 0
          by (metis FlatA_head_s__eq__fst_head_s length_greater_0_conv list.distinct(1) list.sel(1) t_minus_front_s__eq__last_t)
     also have "... = (FlatA(t)\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst(last(s)\<^sub>t)"
          using assms
          by (metis FlatA_t_minus_front_s__eq__FlatA_t_minus_FlatA_front_s)
     also have "... = (FlatA(t)\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t)\<^sub>t) -\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t"
          by (metis FlatA_last_s__eq__fst_last_s assms(2))
     also have "... = FlatA(t)\<^sub>t -\<^sub>t (FlatA(front(s)\<^sub>t)\<^sub>t ^\<^sub>t FlatA([last(s)\<^sub>t])\<^sub>t)"
          by (metis FlatA_last_s__eq__fst_last_s FlatA_s_cat_t__eq__Flat_s_cat_Flat_t FlatA_t_minus_FlatA_s__eq__FlatA_t_minus_front_s__minus__FlatA_last_s `FlatA(t -\<^sub>t front(s)\<^sub>t)\<^sub>t -\<^sub>t fst (last(s)\<^sub>t) = (FlatA(t)\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst (last(s)\<^sub>t)` append_butlast_last_id assms(1) assms(2) assms(3) less_nat_zero_code list.size(3))
     also have "... = FlatA(t)\<^sub>t -\<^sub>t FlatA(front(s)\<^sub>t ^\<^sub>t [last(s)\<^sub>t])\<^sub>t"
          by (metis FlatA_s_cat_t__eq__Flat_s_cat_Flat_t)
     also have "... = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t"
          using assms
          by (metis append_butlast_last_id length_greater_0_conv)
     finally show ?thesis .
     qed

     next
        show "length s < length t \<Longrightarrow> length s < length t" by auto qed
     then
        show "FlatA(difA(t,s)\<^sub>t)\<^sub>t = FlatA(t)\<^sub>t -\<^sub>t FlatA(s)\<^sub>t" by (simp)
qed

lemma length_tail_t_minus_s__eq__length_t_minus_s_plus_one:
  assumes "s <\<^sub>t t"
  shows "length(tail(t-\<^sub>ts)\<^sub>t) = length(t-\<^sub>ts) - 1"
  by (auto)

lemma length_t_minus_s__eq__length_t_minus_length_s:
  assumes "s <\<^sub>t t"
  shows "length(t -\<^sub>t s) = length(t) - length(s)"
  by (metis length_drop minusList_def)

text {* Lemma 26 *}
lemma length_difA_t_s__eq__length_t_minus_length_s_plus_one:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0"
  shows "length(difA(t,s)\<^sub>t) = (length t - length s) + 1"
proof -
  have "length(difA(t,s)\<^sub>t) = length(tail(t-\<^sub>t front(s)\<^sub>t)\<^sub>t) + 1"
      by (simp add:difA_def)
  also have "... = length(t-\<^sub>t front(s)\<^sub>t) - 1 + 1"
      by auto
  also have "... = length(t-\<^sub>t front(s)\<^sub>t)"
      by (metis (no_types, hide_lams) Ex_list_of_length One_nat_def append_butlast_last_id assms(1) calculation length_append length_butlast list.size(4) list_minus_empty list_minus_extended prefix_def sequence_strict_prefix)
  also have "... = length(t) - length(front(s)\<^sub>t)"
      using assms
      by (simp add:length_t_minus_s__eq__length_t_minus_length_s)
  also have "... = length(t) - length(s) + 1"
      using assms
      by (metis (erased, hide_lams) Suc_eq_plus1 Suc_pred `length (t -\<^sub>t front(s)\<^sub>t) = length t - length (front(s)\<^sub>t)` `length (t -\<^sub>t front(s)\<^sub>t) - 1 + 1 = length (t -\<^sub>t front(s)\<^sub>t)` diff_diff_left length_butlast monoid_add_class.add.left_neutral)
  finally show ?thesis .
qed

lemma difA_t_s__eq__list_u_v:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "fst(last(s)\<^sub>t) \<le>\<^sub>t fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)"
  shows "difA(t,s)\<^sub>t = [(u,v)] \<longleftrightarrow> (fst(head(t-\<^sub>t front(s)\<^sub>t)\<^sub>t) -\<^sub>t fst(last(s)\<^sub>t)) = u \<and> snd(head(t-\<^sub>tfront(s)\<^sub>t)\<^sub>t) = v \<and> tail(t-\<^sub>tfront(s)\<^sub>t)\<^sub>t = []"
  by (metis (no_types, hide_lams) append_Nil append_Nil2 difA_def list.distinct(1) list.sel(1) list.sel(3) prod.inject tl_append2)

text {* Corresponds to Lemma 15. *}
lemma difA_t_s__eq__list_empty_snd_last_s__iff__t__eq__s:
  assumes "front(s)\<^sub>t <\<^sub>t t" and "length s > 0" and "fst(last(s)\<^sub>t) \<le>\<^sub>t fst(head(t -\<^sub>t front(s)\<^sub>t)\<^sub>t)"
  shows "difA(t,s)\<^sub>t = [([],snd(last(s)\<^sub>t))] \<longleftrightarrow> t=s"
  using assms
  apply (simp add:difA_t_s__eq__list_u_v)
  apply auto
  apply (smt2 append_Nil append_Nil2 append_butlast_last_id butlast.simps(1) butlast_tl length_greater_0_conv list.distinct(1) list.sel(1) list_minus_extended prod.expand sequence_prefix sequence_strict_prefix tl_append2)
  apply (metis append_Nil2 append_butlast_last_id list.sel(1) list_minus_extended)
  apply (metis append_butlast_last_id list.sel(1) list_minus_extended)
  by (metis drop_eq_Nil length_butlast length_tl minusList_def order_refl tl_drop)

text 
{* The stuff below is an attempt at converting between lists and sets of ordered
   pairs. The function definitions work, but there isn't much proved about them. *}

primrec listToSet :: "nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> 'a) set"
where
  "listToSet n [] = {}"
| "listToSet n (x#xs) = {(n, x)} \<union> (listToSet (n+1) xs)"

definition set_to_list :: "(nat \<times> 'a) set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. listToSet 1 l = s)"

definition update_list_set :: "nat \<Rightarrow> (nat \<times> 'a) set \<Rightarrow> (nat \<times> 'a) set"
  where "update_list_set i s = {(n+i,x) | n x.(n,x) \<in> s}"

value "update_list_set 1 {(1,2),(3,4)}"

value "update_list_set 0 {}"

lemma list_to_set_induct[simp]:
  "listToSet i (x#xs) = (listToSet i [x]) \<union> (listToSet (i+1) xs)"
  by auto

lemma list_set_update_no_change:
  shows "listToSet i xs = update_list_set 0 (listToSet i xs)"
  apply (induct xs)
  apply (simp_all add:update_list_set_def)
  apply (auto)
  done

end
(*
lemma "listToSet i xs = update_list_set i (listToSet 0 xs)"
  apply (simp_all add:update_list_set_def)
  apply auto
  apply (rule_tac ?x = "a-i" in exI)
  apply (auto)
  oops

lemma "listToSet (i+1) xs = update_list_set 1 (listToSet i xs)"
  apply (induct_tac i)
  apply (simp_all add:update_list_set_def)
  apply auto
  oops

lemma "\<forall>n.(n, x) \<in> listToSet 1 l \<longrightarrow> n \<le> length l"
  apply (induct l)
  apply auto
  oops

lemma list_to_set_never_greater:
  "\<forall>n. n < i \<longrightarrow> (n,x) \<notin> listToSet i l"
  apply (induct l)
  apply auto
  oops

lemma "\<forall>x. length l \<noteq> 0 \<and> x \<in> {n | n y.(n,y) \<in> listToSet i l} \<longrightarrow> i \<le> x"
  apply auto
  oops

lemma "\<forall>n. (n,x) \<in> listToSet (Suc i) l \<longrightarrow> i < n"
  apply (induct_tac l)
  apply (auto)
  apply (simp add:listToSet_def)
  apply auto
  oops

lemma "\<forall>n. (n,x) \<in> listToSet i l \<longrightarrow> (n+1,x) \<in> listToSet (Suc i) l"
  apply auto
  oops

lemma list_to_set_single: "listToSet i [x] = {(i,x)}"
  apply auto
  done

lemma list_to_set_multiple: "listToSet i (x#xs) = {(i,x)} \<union> listToSet (Suc i) xs"
  apply auto
  done

lemma "\<forall>n.\<exists>m. (n,a) \<in> (listToSet i x) \<and> (m,b) \<in> (listToSet i (x#xs)) \<and> n < m"
  oops

lemma "\<forall>n x. (n,x) \<in> listToSet i xs \<longrightarrow> i \<le> n"
  apply (induct xs)
  apply (metis empty_iff listToSet.simps(1))
  apply (subst list_to_set_multiple)
  apply simp
  apply auto
  apply (simp add:listToSet_def) 
  oops

lemma "{n | n. (n,x) \<in> listToSet 1 l} = {1..length l}"
  apply auto
  unfolding listToSet_def
  sledgehammer
  oops

lemma  set_set_to_list:
   "finite s \<Longrightarrow> listToSet 1 (set_to_list s) = s"
   apply (simp add:set_to_list_def)
   apply (simp add:listToSet_def)

value "set_to_list {(1,a),(3,b)}"

value "sorted_list_of_set {(1,a),(2,b)}"

function setToList :: "nat \<Rightarrow> (nat \<times> 'a) set \<Rightarrow> 'a list"
where
 "setToList n {} = []"
 "setToList n x =

(* where "listToSet n (setToList n ss)"*)

(*where "(listToSet ni (setToList ni s)) = s"*)

(* where "\<exists>li. (setToList ni s) = li \<and> (listToSet ni li) = s" *)

primrec setToList2 :: "nat \<Rightarrow> (nat \<times> 'a) set \<Rightarrow> 'a list"
where
  "setToList2 n {} = []"
| "setToList2 n (xs-{(n,x)}) = x#(setToList (n+1) xs)"

value "setToList 1 {(1,2)}"

value "card (set [1,2,1,3,2])"

value "remdups [1, 2, 1]"
*)
