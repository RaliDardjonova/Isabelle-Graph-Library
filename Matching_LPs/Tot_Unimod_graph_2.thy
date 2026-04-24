theory Tot_Unimod_graph_2
  imports Totally_Unimodular Even_More_Graph_2
begin

context gram_schmidt_floor
begin 

definition perfect_matching_polyhedron where 
  "perfect_matching_polyhedron A b = {x. x \<in> carrier_vec n \<and> A *\<^sub>v x  = b \<and> x \<ge> 0\<^sub>v n}"

lemma pick_from_range_less:
  assumes "i < k"
  shows "pick {0..<k} i = i"
proof -
  have "i < card {0..<k}" 
    by (simp add: assms)
  have "card {a\<in>{0..<k}. a < pick {0..<k} i} = i" 
    by (metis assms card_atLeastLessThan card_pick diff_zero)
  have 2: "{a\<in>{0..<k}. a < pick {0..<k} i} = {a . a < pick {0..<k} i}" 
    by (metis \<open>i < card {0..<k}\<close> atLeast0LessThan basic_trans_rules(19) lessThan_iff pick_in_set_le)
  have "card {a . a < pick {0..<k} i} = pick {0..<k} i" 
    using card_Collect_less_nat by blast
  then show ?thesis 
    using \<open>card {a \<in> {0..<k}. a < pick {0..<k} i} = i\<close> 2 by force
qed

lemma perfect_matching_polyhedron_face:
  assumes "A \<in> carrier_mat nr n"
  assumes "b \<in> carrier_vec nr"
  assumes "(perfect_matching_polyhedron A b) \<noteq> {}"
  shows "face  (pos_polyhedron A b) (perfect_matching_polyhedron A b)"
proof -
 have 2: "(A @\<^sub>r - 1\<^sub>m n) \<in> carrier_mat (nr+n) n" 
    by (meson assms(1) carrier_append_rows one_carrier_mat uminus_carrier_mat)
  have 3: "(b @\<^sub>v 0\<^sub>v n) \<in> carrier_vec (nr+n)"
    by (simp add: assms(2))
  have 1:"(A, b) = sub_system (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n) {0..<nr}" 
  proof -
    have 7: "submatrix (A @\<^sub>r - 1\<^sub>m n) {0..<nr} UNIV = 
            submatrix A {0..<nr} UNIV @\<^sub>r submatrix (- 1\<^sub>m n) 
                                         ((\<lambda> i. i - nr) ` ({0..<nr} - {0..<nr})) UNIV"
      using  gram_schmidt_floor.append_submatrix_is_submatrix assms(1) one_carrier_mat uminus_carrier_iff_mat
      
      by (metis gram_schmidt_floor.append_submatrix_is_submatrix assms(1) one_carrier_mat uminus_carrier_iff_mat)
    have "submatrix A {0..<nr} UNIV = A" 
      by (metis assms(1) assms(2) itself_is_subsyst_set_idcs prod.sel(1) sub_system_fst)
    have "submatrix (- 1\<^sub>m n) ((\<lambda> i. i - nr) ` ({0..<nr} - {0..<nr})) UNIV =
        submatrix (- 1\<^sub>m n) {} UNIV" 
      by simp
    then have 8: "A = submatrix (A @\<^sub>r - 1\<^sub>m n) {0..<nr} UNIV" 
      by (smt (verit, best) "7" \<open>submatrix A {0..<nr} UNIV = A\<close> assms(1) index_uminus_mat(3)
          carrier_mat_triv dim_col_submatrix_UNIV empty_set_submatrix_iz_zero_mat
          gram_schmidt_floor.append_mat_empty index_one_mat(3) index_zero_mat(2))

    have 9:"b = vec_of_list (nths (list_of_vec (b @\<^sub>v 0\<^sub>v n)) {0..<nr})" 
    proof
      have 4: "dim_vec (snd (sub_system (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n) {0..<nr})) = 
            card {i. i < dim_vec (b @\<^sub>v 0\<^sub>v n) \<and> i \<in> {0..<nr}}" 
        using dim_subsyst_vec 
        by blast
      have "dim_vec (b @\<^sub>v 0\<^sub>v n) = nr + n" 
        by (simp add: assms(2))
      then have "{i. i < dim_vec (b @\<^sub>v 0\<^sub>v n) \<and> i \<in> {0..<nr}} = {0..<nr}" 
        by fastforce
     
      then have " card {i. i < dim_vec (b @\<^sub>v 0\<^sub>v n) \<and> i \<in> {0..<nr}} = card {0..<nr}" 
        by presburger
      then have 5: "dim_vec (vec_of_list (nths (list_of_vec (b @\<^sub>v 0\<^sub>v n)) {0..<nr})) = nr" 
        by (metis (no_types, lifting) 4 card_atLeastLessThan diff_zero dim_subsyst_vec
            dim_vec nths_list_pick_vec_same) 
      then show 4:"dim_vec b = dim_vec (vec_of_list (nths (list_of_vec (b @\<^sub>v 0\<^sub>v n)) {0..<nr}))"
        by (metis assms(2) carrier_vecD)
      fix i
      assume asmi: "i < dim_vec (vec_of_list (nths (list_of_vec (b @\<^sub>v 0\<^sub>v n)) {0..<nr}))"
      then have asmi': "i < dim_vec b" 
        using 4 by presburger
      obtain k where k: "k < dim_vec (b @\<^sub>v 0\<^sub>v n) \<and> k \<in> {0..<nr} \<and> 
          row (fst (sub_system (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n) {0..<nr})) i = row (A @\<^sub>r - 1\<^sub>m n) k 
          \<and> (snd (sub_system (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n) {0..<nr})) $ i = (b @\<^sub>v 0\<^sub>v n) $ k \<and> 
      k = pick {0..<nr} i"
        using exist_index_in_A[of "(A @\<^sub>r - 1\<^sub>m n)" "(b @\<^sub>v 0\<^sub>v n)" i "{0..<nr}"] 2 3
        by (metis \<open>dim_vec (b @\<^sub>v 0\<^sub>v n) = nr + n\<close> asmi carrier_matD(1) sub_system_snd)
      
      have 6: "(vec_of_list (nths (list_of_vec (b @\<^sub>v 0\<^sub>v n)) {0..<nr})) $v i = (b @\<^sub>v 0\<^sub>v n) $ k"
        by (metis k sub_system_snd)     
      have "pick {0..<nr} i = i"  
        using pick_from_range_less 5 asmi by presburger
      then have "(b @\<^sub>v 0\<^sub>v n) $ k = (b @\<^sub>v 0\<^sub>v n) $ i" 
        using k by auto
      have "(b @\<^sub>v 0\<^sub>v n) $ i = b $ i" 
        by (simp add: asmi' trans_less_add1)
      then show "b $v i = vec_of_list (nths (list_of_vec (b @\<^sub>v 0\<^sub>v n)) {0..<nr}) $v i" 
        using \<open>(b @\<^sub>v 0\<^sub>v n) $v k = (b @\<^sub>v 0\<^sub>v n) $v i\<close> 6 by presburger
    qed
    show "(A, b) = sub_system (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n) {0..<nr}"
      unfolding sub_system_def using 8 9 
      by blast
  qed
  have "{x. x \<in> carrier_vec n \<and> A *\<^sub>v x = b \<and> x \<ge> 0\<^sub>v n} = 
              {x. A *\<^sub>v x = b \<and> x \<in> (pos_polyhedron A b)}" 
    unfolding pos_polyhedron_def 
    by fast
  then have "(perfect_matching_polyhedron A b) = 
           {x. A *\<^sub>v x = b \<and> x \<in> (pos_polyhedron A b)}" 
    unfolding perfect_matching_polyhedron_def by auto
  have "pos_polyhedron A b = polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n)" 
    using assms(1) assms(2) pos_polyh_is_polyh by presburger
 
  then have "face (polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n)) (perfect_matching_polyhedron A b)" 
    using char_face2[OF 2 3 1] 
    using \<open>perfect_matching_polyhedron A b = {x. A *\<^sub>v x = b \<and> x \<in> pos_polyhedron A b}\<close> 
      \<open>pos_polyhedron A b = local.polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n)\<close> assms(3) by presburger
  then show ?thesis 
    using \<open>pos_polyhedron A b = local.polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n)\<close> by presburger
qed

lemma face_int_polyhedron_int_matrix:
   fixes A :: "'a  mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
 assumes "(A', b') = sub_system A b I'"
 assumes " F = {x.  x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b}"
  assumes "A \<in> \<int>\<^sub>m"
  assumes "b \<in> \<int>\<^sub>v"
  shows "((A' @\<^sub>r (-A')) @\<^sub>r A) \<in> \<int>\<^sub>m" "((b' @\<^sub>v (-b')) @\<^sub>v b) \<in> \<int>\<^sub>v"
proof -
  have "A' \<in> \<int>\<^sub>m" 
    by (metis assms(4) assms(6) prod.simps(1) sub_system_def submatrix_int_mat)
  then show "((A' @\<^sub>r (-A')) @\<^sub>r A) \<in> \<int>\<^sub>m" 
    by (metis assms(1) assms(4) assms(6) b carrier_mat_triv gram_schmidt.append_int_mat_is_int gram_schmidt.face_is_polyhedron'(3) minus_in_Ints_mat_iff uminus_carrier_iff_mat)
  have "b' \<in> \<int>\<^sub>v" 
    using assms(4) unfolding sub_system_def
    using subvec_int_int 
    using assms(7) by blast
  then show "((b' @\<^sub>v (-b')) @\<^sub>v b) \<in> \<int>\<^sub>v" 
    by (meson append_int_vec_is_int assms(7) carrier_vec_dim_vec minus_in_Ints_vec_iff)
qed

lemma face_is_int_polyhedron:
   fixes A :: "'a mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "face P F" 
 assumes "A \<in> \<int>\<^sub>m"
  assumes "b \<in> \<int>\<^sub>v"
  obtains A' b' where "F = polyhedron A' b'" "dim_row A' = dim_vec b'" "dim_col A' = n"
                      "A' \<in> \<int>\<^sub>m" "b' \<in> \<int>\<^sub>v"
proof -
  obtain  A' b' I'  where  A'_b': "(A', b') = sub_system A b I'" 
                      " F = {x.  A' *\<^sub>v x = b' \<and> x \<in> P}"
    using char_face1[of A nr b F]
    using A P_def assms(4) b by blast
  have 1: "F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b}" 
    using A'_b'(2) unfolding P_def polyhedron_def by auto
  show ?thesis
    using face_is_polyhedron''[OF assms(1) assms(2) A'_b'(1) 1 ]
      face_int_polyhedron_int_matrix[OF assms(1) assms(2) A'_b'(1) 1 assms(5) assms(6)]
    using that by presburger
qed

lemma int_poly_face_int:
 fixes A :: "'a mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b" 
  assumes "int_polyh P"
  assumes "face P F"
  assumes "A \<in> \<int>\<^sub>m"
  assumes "b \<in> \<int>\<^sub>v" 
  shows "int_polyh F" 
proof -
  have "P = integer_hull P"
    using assms(4) gram_schmidt_floor.int_polyh_def by blast
  have "P \<subseteq> carrier_vec n" unfolding P_def polyhedron_def 
    by blast 
  then have "(\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))"
  using P_int_then_face_int \<open>P = integer_hull P\<close> by presburger
  have "(\<forall> F'. face F F' \<longrightarrow> (\<exists> x \<in> F'. x \<in> \<int>\<^sub>v))"
    using P_def P_int_then_face_int \<open>P = integer_hull P\<close> \<open>P \<subseteq> carrier_vec n\<close> 
      assms(1) assms(5) b face_trans by presburger
  obtain A' b'  where "F = polyhedron A' b'" "dim_row A' = dim_vec b'" "dim_col A' = n"
                      "A' \<in> \<int>\<^sub>m" "b' \<in> \<int>\<^sub>v" using face_is_int_polyhedron 
    by (metis P_def assms(1) assms(5) assms(6) assms(7) b)
  
  then have "F = integer_hull F" using face_iff_int_polyh 
    using \<open>\<forall>F'. face F F' \<longrightarrow> (\<exists>x\<in>F'. x \<in> \<int>\<^sub>v)\<close> carrier_vec_dim_vec by blast
  then show ?thesis unfolding int_polyh_def by auto
qed
end

context bipartite_matching_lp
begin

no_notation Finite_Cartesian_Product.vec_nth (infixl "$" 90)
no_notation inner (infix "\<bullet>" 70)

lemma dim_col_incidence_mat:
  shows "dim_col (incidence_matrix) = card G" 
  unfolding incidence_matrix_def by auto

lemma dim_row_incidence_mat:
  shows "dim_row (incidence_matrix) = (card (Vs G))" 
  unfolding incidence_matrix_def
  using n_def by simp

lemma elems_incidence_one_zero:
  assumes "i < card (Vs G)"
  assumes "j < card G"
  shows "(incidence_matrix) $$ (i,j) = 0 \<or> (incidence_matrix) $$ (i,j) = 1"  
  unfolding incidence_matrix_def of_bool_def 
  by (simp add: assms(1,2) n_def)

lemma one_then_in_edge:
  assumes "i < card (Vs G)"
  assumes "j < card G"
  assumes "incidence_matrix $$ (i,j) = 1"
  shows "Vs_enum_inv i \<in> from_nat_into G j"
proof -
  have "incidence_matrix $$ (i,j) = of_bool (Vs_enum_inv i \<in> from_nat_into G j)"
    by (simp add: assms(1,2) incidence_matrix_def n_def)
  then show "Vs_enum_inv i \<in> from_nat_into G j" 
    unfolding of_bool_def using assms(3)
    by argo
qed

lemma diff_verts_enum:
  assumes "i < card (Vs G)"
  assumes "j < card (Vs G)"
  assumes "i \<noteq> j"
  shows "Vs_enum_inv i \<noteq> Vs_enum_inv j"
proof -
  have "finite (Vs G)" 
    by (metis assms(1) card.infinite less_nat_zero_code)
  then show ?thesis 
    by (metis Vs_enum_inv assms(1,2,3) n_def)
qed

lemma at_most_two_ones2:
  assumes "k < card G"
  assumes "i < (card (Vs G))"
  assumes "j < (card (Vs G))"
  assumes "i \<noteq> j"
  assumes " (incidence_matrix) $$ (i, k) = 1 \<and> (incidence_matrix) $$ (j, k) = 1"
  shows "(\<forall> t < card (Vs G). (t\<noteq>i \<and> t \<noteq> j) \<longrightarrow> (incidence_matrix) $$ (t,k) = 0)"
proof safe
  fix t
  assume asm: "t < card (Vs G)" "t \<noteq> i" "t \<noteq> j"
  show "(incidence_matrix) $$ (t,k) = 0"
  proof(rule ccontr)
    assume "(incidence_matrix) $$ (t, k) \<noteq> 0" 
    then have "(incidence_matrix) $$ (t, k) = 1" 
      by (meson asm(1) assms(1) elems_incidence_one_zero)
    then have 1: "Vs_enum_inv t \<in> from_nat_into G  k" 
      using asm(1) assms(2) one_then_in_edge
      using assms(1) by blast
    have 2: "Vs_enum_inv i \<in> from_nat_into G  k" 
      using assms(1-3) assms(5)one_then_in_edge
      by blast
    have 3: "Vs_enum_inv j \<in> from_nat_into G k" 
      using assms(1-5) one_then_in_edge
      by blast
    have "card (from_nat_into G k) \<noteq> 2"
    proof(cases "infinite (from_nat_into G k)")
      case True
      then show ?thesis 
        by simp
    next
      case False
      have "{Vs_enum_inv i, Vs_enum_inv j, Vs_enum_inv t} \<subseteq> 
           from_nat_into G k"
        by (simp add: 1 2 3)
      then show ?thesis
        by (metis  diff_verts_enum assms(3) assms(2) asm(1) card_2_iff' "2" "3" "1" asm(2) assms(4) asm(3))
    qed
    have "from_nat_into G  k \<in> G"
      by (metis assms(1) from_nat_into_G_E_aux)
    then show False 
      using card_edge[of G] \<open>card (from_nat_into G k) \<noteq> 2\<close> assms(1) by fastforce
  qed
qed

lemma dim_row_mat_less_card_I:
  assumes "finite I" 
  shows "dim_row (submatrix A I J) \<le> card I" 
proof -
  have "{i. i < dim_row A \<and> i \<in> I} \<subseteq> I" by auto
  then have "card {i. i < dim_row A \<and> i \<in> I} \<le> card I" 
    using assms card_mono by blast
  then show ?thesis 
    by (simp add: dim_submatrix(1))
qed

lemma exist_index_in_submat:
  assumes "B = submatrix A I UNIV"
  assumes "j < dim_row B"
  shows "\<exists> i < dim_row A. i \<in> I \<and> row B j = row A i  \<and> i = pick I j"
proof -
  have "(pick I j) < dim_row A"  
    by (metis assms(1) assms(2) dim_submatrix(1) pick_le)
  moreover have "(pick I j) \<in> I" 
    apply(cases "finite I") 
    using  dim_row_mat_less_card_I pick_in_set_le 
     apply (metis assms(1) assms(2) order_trans_rules(22))
    using pick_in_set_inf by auto
  ultimately show ?thesis 
    by (metis (no_types, lifting) assms dim_submatrix(1) row_submatrix_UNIV)
qed

lemma submatrix_not_more_than_two:
  assumes "k < dim_col B"
  assumes "i < dim_row B"
  assumes "j < dim_row B"
  assumes "i \<noteq> j"
  assumes "B = submatrix (incidence_matrix) I J"
  assumes "B $$ (i, k) = 1 \<and> B $$ (j, k) = 1"
  shows "(\<forall> t < dim_row B. (t\<noteq>i \<and> t \<noteq> j) \<longrightarrow> B $$ (t,k) = 0)"
proof safe
  fix t
  assume asm: "t < dim_row B" "t \<noteq> i" "t \<noteq> j"
  obtain i1 where i1: "row (incidence_matrix) i1 = 
        row (submatrix (incidence_matrix) I UNIV) i \<and>
        i1 < dim_row (incidence_matrix) \<and> 
        i1 = pick I i"
    using exist_index_in_submat 
    by (metis (no_types, lifting) assms(2,5) dim_submatrix(1))
  obtain j1 where j1: "row (incidence_matrix) j1 = 
        row (submatrix (incidence_matrix) I UNIV) j \<and> 
        j1 < dim_row (incidence_matrix) \<and> 
        j1 = pick I j"
    using exist_index_in_submat
    by (metis (no_types, lifting) assms(3,5) dim_submatrix(1))
  obtain t1 where t1: "row (incidence_matrix) t1 = 
        row (submatrix (incidence_matrix) I UNIV) t \<and> 
        t1 < dim_row (incidence_matrix) \<and> 
        t1 = pick I t"
    using exist_index_in_submat
  by (metis (no_types, lifting) asm(1) assms(5) dim_submatrix(1))
  have "dim_col B = card {i. i < dim_col (incidence_matrix) \<and> i \<in> J}" 
    using assms(5) dim_submatrix(2) by blast
  then obtain k1 where k1: "col (incidence_matrix) k1 = 
         col (submatrix (incidence_matrix) UNIV J) k \<and>
         k1 < dim_col (incidence_matrix) \<and> 
         k1 = pick J k" 
    using pick_le col_submatrix_UNIV 
    by (metis (no_types, lifting) Collect_cong \<open>k < dim_col B\<close>)
  have "k1 < card G" 
    using dim_col_incidence_mat k1 by metis
  have "i1 < (card (Vs G))"
    using dim_row_incidence_mat i1 by metis
  have "j1 < (card (Vs G))" 
    using dim_row_incidence_mat j1 by metis
  have "pick I i \<noteq> pick I j" 
    by (metis (no_types, lifting) assms(2,3,4,5) basic_trans_rules(22)
        dim_row_mat_less_card_I dim_submatrix(1) exist_index_in_submat
        pick_eq_iff_inf pick_index)
  then have "i1 \<noteq> j1" 
    using i1 j1 by blast
  have "(incidence_matrix) $$ (pick I i, pick J k) = B  $$ (i,k)" 
    by (metis (no_types, lifting) assms(1,2,5) dim_submatrix(1,2) submatrix_index)
  then have "(incidence_matrix) $$ (i1, k1) = 1" 
    using assms(6) i1 k1 by presburger
  have "(incidence_matrix) $$ (pick I j, pick J k) = B  $$ (j,k)"
    by (metis (no_types, lifting) assms(1,3,5) dim_submatrix(1,2)
        submatrix_index)
  then have "(incidence_matrix) $$ (j1, k1) = 1" 
    using assms(6) j1 k1 by presburger
  then have 1: "(\<forall> t < card (Vs G). (t\<noteq>i1 \<and> t \<noteq> j1) \<longrightarrow> (incidence_matrix) $$ (t,k1) = 0)"
    using \<open>i1 < card (Vs G)\<close> \<open>i1 \<noteq> j1\<close> \<open>incidence_matrix $$ (i1, k1) = 1\<close>
      \<open>j1 < card (Vs G)\<close> \<open>k1 < m\<close> at_most_two_ones2 by blast
  have "pick I t \<noteq> pick I i"
    using  asm(1,2) assms(3,6) diff_is_0_eq diff_less_mono dim_row_mat_less_card_I less_irrefl
        not_less not_less_iff_gr_or_eq not_less_zero pick_mono_inf pick_mono_le
    by (metis assms(2,5))
  have "pick I t \<noteq> pick I j"
    by (metis asm(1,3) assms(3,5) diff_is_0_eq diff_less_mono dim_row_mat_less_card_I less_irrefl 
        not_less not_less_iff_gr_or_eq not_less_zero pick_mono_inf pick_mono_le)
  then have "(incidence_matrix) $$ (t1, k1) = 0" 
    by (metis 1 \<open>pick I t \<noteq> pick I i\<close> dim_row_incidence_mat i1 j1 t1)
  show "B $$ (t,k) = 0"
    by (metis (no_types, lifting) \<open>incidence_matrix $$ (t1, k1) = 0\<close> asm(1) assms(1,5) 
        dim_submatrix(1-2) k1 submatrix_index t1)
qed



lemma submatrix_incidence_zero_or_one:
  assumes "k < dim_col B"
  assumes "i < dim_row B"
  assumes "B = submatrix (incidence_matrix) I J"
  shows "B $$ (i, k) = 1 \<or> B $$ (i, k) = 0"
proof -
  have 1: "B $$ (i, k) = (incidence_matrix) $$ (pick I i, pick J k)"
    by (metis (no_types, lifting) assms(1,2,3) carrier_matD(1,2) mat_carrier
        submatrix_def submatrix_index)
  have "pick I i < card (Vs G)" 
    
    by (metis (no_types, lifting) Collect_cong assms(2,3) carrier_matD(1)
        incidence_matrix_carrier_mat mat_carrier n_def pick_le
        submatrix_def)
  have "pick J k < card G" 
    by (metis (no_types, lifting) Collect_cong assms(1,3) carrier_matD(2)
        incidence_matrix_carrier_mat mat_carrier pick_le submatrix_def)
  have "(incidence_matrix) $$ (pick I i, pick J k) = 1 \<or> 
        (incidence_matrix) $$ (pick I i, pick J k) = 0"
    using \<open>pick I i < card (Vs G)\<close> \<open>pick J k < m\<close>
      elems_incidence_one_zero bipartite_matching_lp_axioms
    by blast
  then show ?thesis
    using 1 by presburger
qed

lemma is_bipartite_submatrix_det_unimod:
  assumes "B = submatrix (incidence_matrix) I J" 
  shows "det B \<in> {-1, 0, 1}" using assms(1)
proof(induct "dim_row B" arbitrary: B I J rule: less_induct)
  case less
  show ?case
  proof(cases "dim_row B \<noteq> dim_col B")
    case True
    then show ?thesis 
      unfolding Determinant.det_def  
      by (meson insertCI)
  next
    case False
    have 1: "dim_row B = dim_col B" using False by auto
    then show ?thesis 
    proof(cases "carrier class_ring = {\<zero>\<^bsub>class_ring\<^esub> :: real}")
      case True
      have "carrier class_ring = {\<zero>\<^bsub>class_ring\<^esub> :: real}" 
        using True 
        by linarith
      then have "det B = 0" 
        by auto
      then show ?thesis 
        by blast
    next
      case False
      show ?thesis
      proof(cases "\<exists> j < dim_col B. col B j = 0\<^sub>v (dim_row B)")
        case True
        obtain j where " j < dim_col B \<and> col B j = 0\<^sub>v (dim_row B)" 
          using True by blast
        have 2:"B \<in> carrier_mat (dim_row B) (dim_row B)" 
          by (metis "1" carrier_matI)
        have "0\<^sub>v (dim_row B) \<in> (set (cols B))" 
          by (metis True cols_length cols_nth in_set_conv_nth)
        have 3:"\<zero>\<^bsub>module_vec TYPE(real) (dim_row B)\<^esub>\<in> set (cols B)" 
          by (metis \<open>0\<^sub>v (dim_row B) \<in> set (cols B)\<close> module_vec_simps(2))
        have 4:"Module.module class_ring (module_vec TYPE(real) (dim_row B))" 
          using vec_module by blast
        have 5:" carrier class_ring \<noteq> {\<zero>\<^bsub>class_ring\<^esub> ::real}" using False
          by simp
        have "module.lin_dep class_ring
     (module_vec TYPE(real) (dim_row B))
     (set (cols B))" 
          using module.zero_lin_dep[OF 4 3 5]
          by fastforce
        then have "det B = 0" 
          using idom_vec.lin_dep_cols_imp_det_0[OF 2] 
          by blast
        then show ?thesis 
          by force 
      next
        case False
        show ?thesis
        proof(cases "\<exists>j<dim_col B. \<exists> i < dim_row B. col B j = unit_vec (dim_row B) i")
          case True
          have 2:"B \<in> carrier_mat (dim_row B) (dim_row B)" 
            by (metis "1" carrier_matI)
          obtain j i where i_j:"j<dim_col B \<and> i < dim_row B \<and> col B j = unit_vec (dim_row B) i"
            using True by auto
          have 3: "j < dim_row B" using i_j 
            using "1" by presburger
          have 10: "det B = (\<Sum>k<dim_row B. B $$ (k,j) * cofactor B k j)"
            using laplace_expansion_column[OF 2 3] 
            by presburger
          have "\<forall>k<dim_row B. k \<noteq> i \<longrightarrow> B $$ (k,j) = 0" 
          proof safe
            fix k 
            assume asm: "k < dim_row B" "k\<noteq>i"
            have "B $$ (k,j) = col B j $ k" 
              by (metis asm(1) i_j index_col)
            have "unit_vec (dim_row B) i $ k = 0"
              unfolding unit_vec_def 
              by (simp add: i_j asm)
            show "B $$ (k, j) = 0" 
              by (metis \<open>B $$ (k, j) = col B j $v k\<close> \<open>unit_vec (dim_row B) i $v k = 0\<close> i_j)
          qed
          then have "(\<Sum>k \<in> {0..<dim_row B}. B $$ (k,j) * cofactor B k j) =
               B $$ (i,j) * cofactor B i j" 
            by (metis (mono_tags, lifting) atLeast0LessThan gram_schmidt_floor.only_one_nonzero_is_sum 
                finite_atLeastLessThan i_j lessThan_iff vector_space_over_itself.scale_eq_0_iff)
          then have 13: "det B = B $$ (i,j) * cofactor B i j" 
            by (metis 10 atLeast0LessThan)
          have 8:"cofactor B i j = (-1)^(i+j) * det (mat_delete B i j)" 
            using Determinant.cofactor_def by blast
          have 9:"mat_delete B i j = submatrix (incidence_matrix) (I - {pick I i}) (J - {pick J j})"
            using gram_schmidt_floor.mat_delete_is_submatrix i_j less(2) by blast
          have 11: "dim_row ( submatrix (incidence_matrix) (I - {pick I i}) (J - {pick J j})) < 
                    dim_row B" 
            by (metis "9" bot_nat_0.not_eq_extremum diff_less i_j less_nat_zero_code 
                less_one mat_delete_dim(1))
          have "det (submatrix (incidence_matrix) (I - {pick I i}) (J - {pick J j})) \<in> {-1, 0, 1}" 
            using 11 less(1) by presburger
          then have "det (mat_delete B i j) \<in> {-1, 0, 1}" 
            using "9" by presburger
          then have 12: "cofactor B i j \<in> {-1, 0, 1}" 
            using 8 insert_iff mult_cancel_right2 mult_minus1 
              singletonD square_eq_1_iff vector_space_over_itself.scale_eq_0_iff
            by fastforce
          have "B $$ (i,j) = col B j $ i" 
            by (metis i_j index_col)
          have "unit_vec (dim_row B) i $ i = 1" 
            unfolding unit_vec_def 
            by (simp add: i_j)
          then have "B $$ (i,j) = 1" 
            by (simp add: \<open>B $$ (i, j) = col B j $v i\<close> i_j)
          then show ?thesis 
            by (metis 12 13 mult_cancel_right2)
        next
          case False             
          show ?thesis
          proof(cases "dim_row B = 0")
            case True
            have "det B = 1" using det_dim_zero 
              by (metis "1" True carrier_mat_triv)
            then show ?thesis by auto
          next
            case False
            have 4:"dim_row B > 0" using False by auto
            have 5:"\<forall> k < dim_col B. \<exists> i < dim_row B. \<exists> j < dim_row B. 
                    B $$ (i, k) = 1 \<and> B $$ (j, k) = 1 \<and> i\<noteq>j" 
              apply safe
              apply (rule ccontr)
            proof -
              fix k
              assume "k < dim_col B"
              assume asm_not: "\<not> (\<exists>i<dim_row B. \<exists>j<dim_row B.
                               B $$ (i, k) = 1 \<and> B $$ (j, k) = 1 \<and> i \<noteq> j)"
              have "col B k \<noteq> 0\<^sub>v (dim_row B)"
                using `\<not> (\<exists>j<dim_col B. col B j = 0\<^sub>v (dim_row B))` 
                using \<open>k < dim_col B\<close> by blast
              have "\<exists> i < dim_row B. B $$ (i, k) = 1"
              proof(rule ccontr)
                assume "\<not> (\<exists>i<dim_row B. B $$ (i, k) = 1)"
                then have "\<forall>i<dim_row B. B $$ (i, k) = 0" 
  using \<open>k < dim_col B\<close> less(2) submatrix_incidence_zero_or_one
  by blast
    then have "\<forall>i<dim_row B. col B k $ i = 0"
                  by (metis \<open>k < dim_col B\<close> index_col)
                then have "col B k = 0\<^sub>v (dim_row B)"
                  unfolding zero_vec_def 
                  by (metis Matrix.zero_vec_def dim_col dim_vec eq_vecI index_zero_vec(1))
                then show False
                  using `col B k \<noteq> 0\<^sub>v (dim_row B)` by auto
              qed
              then obtain i where i: "i < dim_row B \<and> B $$ (i, k) = 1" by auto
              have 13: "\<forall> j < dim_row B. i \<noteq> j \<longrightarrow>  B $$ (j, k) = 0" 
              proof safe
                fix j
                assume asm: "j < dim_row B" "i \<noteq> j"
                show " B $$ (j, k) = 0"
                proof(rule ccontr)
                  assume "B $$ (j, k) \<noteq> 0"
                  then have "B $$ (j, k) = 1" 
                    using submatrix_incidence_zero_or_one
                    using \<open>k < dim_col B\<close> asm(1) less.prems by blast
                  then show False 
                    using asm_not i asm(1) asm(2) by blast
                qed
              qed
              have "col B k = unit_vec (dim_row B) i" 
              proof 
                show 14: "dim_vec (col B k) = dim_vec (unit_vec (dim_row B) i)"
                  by (metis dim_col index_unit_vec(3))
                fix ia
                assume "ia < dim_vec (unit_vec (dim_row B) i)" 
                then show "col B k $v ia = unit_vec (dim_row B) i $v ia" 
                  by (metis 13 14 i \<open>k < dim_col B\<close> dim_col index_col index_unit_vec(1))
              qed
              then show False using `\<not> (\<exists>j<dim_col B. \<exists>i<dim_row B. col B j = unit_vec (dim_row B) i)`
                using \<open>i < dim_row B \<and> B $$ (i, k) = 1\<close> \<open>k < dim_col B\<close> by blast
            qed
          
            let ?u = "vec (dim_row B) 
                      (\<lambda> i. if Vs_enum_inv (pick I i) \<in> R then (1::real)  else -1)"
            define u where "u =?u" 
            have "\<forall> i < dim_row B. ?u $ i = 1 \<or> ?u $ i = -1" 
              by simp
            then have 32:"?u \<noteq> 0\<^sub>v (dim_row B)" 
              by (metis "4" class_field.neg_1_not_0 class_field.zero_not_one index_zero_vec(1))
            have "\<forall> t < dim_col B. col B t \<bullet> ?u = 0"
            proof safe
              fix t
              assume t: "t < dim_col B"
              obtain i j where i_j: "B $$ (i,t) = 1" 
                "B $$ (j, t) = 1"
                "i < dim_row B" 
                "j < dim_row B" "i \<noteq> j" 
                using 5 t by blast
              have 6:"graph_invar G" 
                by (metis graph) 
              have "\<forall>k < dim_row B. (k \<noteq> i \<and> k \<noteq> j) \<longrightarrow> B $$ (k,t) = 0" 
                using i_j(1,2,3,4,5) less(2) submatrix_not_more_than_two t
                by blast
              then have 15: "\<forall>k < dim_row B. (k \<noteq> i \<and> k \<noteq> j) \<longrightarrow> col B t $ k = 0" 
                by (metis index_col t)
              have 21: "col B t \<bullet> ?u = sum (\<lambda> k. (col B t $ k) * (?u $ k)) {0..<dim_row B}"
                unfolding scalar_prod_def 
                by (metis dim_vec)
              have 19: "sum (\<lambda> k. (col B t $ k) * (?u $ k)) {0..<dim_row B} = 
                        (col B t $ i) * (?u $ i) + (col B t $ j) * (?u $ j)" 
              proof -
                have 17: "sum (\<lambda> k. (col B t $ k) * (?u $ k)) {0..<dim_row B} = 
                      sum (\<lambda> k. (col B t $ k) * (?u $ k)) ({0..<dim_row B} - {i,j}) 
                       + sum (\<lambda> k. (col B t $ k) * (?u $ k)) {i,j}" 
                  by (meson atLeastLessThan_iff empty_subsetI finite_atLeastLessThan i_j(3) i_j(4) 
                      insert_subset sum.subset_diff zero_order(1))
                have 16: "\<forall> k \<in> ({0..<dim_row B} - {i,j}). (col B t $ k) * (?u $ k) = 0" 
                  by (metis Diff_iff 15 atLeastLessThan_iff insertCI 
                      vector_space_over_itself.scale_eq_0_iff)
                have 18: "sum (\<lambda> k. (col B t $ k) * (?u $ k)) ({0..<dim_row B} - {i,j}) = 0" 
                  using 16 
                  by (intro sum.neutral) 
                have "sum (\<lambda> k. (col B t $ k) * (?u $ k)) {i,j} = 
                      (col B t $ i) * (?u $ i) + (col B t $ j) * (?u $ j)"
                  by (meson i_j(5) sum_two_elements)
                then show ?thesis 
                  using "17" "18" by linarith
              qed
              have 20: "(col B t $ i) = 1 \<and> (col B t $ j) = 1" 
                by (metis i_j(1) i_j(2) i_j(3) i_j(4) index_col t)
              have 30: "col B t \<bullet> ?u = (?u $ i) + (?u $ j)" 
                using 19 20 21 
                by (metis (no_types, lifting) mult_cancel_right2)
              have "pick J t < card G" 
                by (metis dim_submatrix(2)dim_col_incidence_mat 
                    less(2) pick_le t)
              have "incidence_matrix $$ (pick I i, pick J t) = 1" 
                by (metis (no_types, lifting) dim_submatrix(1) dim_submatrix(2) i_j(1) i_j(3) 
                    less(2) submatrix_index t)
              then have 23: "Vs_enum_inv (pick I i) \<in> from_nat_into G (pick J t)" 
                by (metis (no_types, lifting) \<open>pick J t < card G\<close> dim_submatrix(1) i_j(3) less(2)
                    exist_index_in_submat dim_row_incidence_mat one_then_in_edge)
              have "incidence_matrix $$ (pick I j, pick J t) = 1"
                by (metis (no_types, lifting) dim_submatrix(1) dim_submatrix(2) i_j(2) i_j(4) 
                    less(2) submatrix_index t)
              then have 24: "Vs_enum_inv (pick I j) \<in> from_nat_into G (pick J t)" 
                by (metis (no_types, lifting) \<open>pick J t < card G\<close> dim_submatrix(1) 
                    exist_index_in_submat dim_row_incidence_mat
                   one_then_in_edge i_j(4) less(2))
              have 22: "from_nat_into G  (pick J t) \<in> G"
                by (metis \<open>pick J t < m\<close> from_nat_into_G_E_aux)
              have 27: "Vs_enum_inv (pick I i) \<noteq> Vs_enum_inv (pick I j)"
                using  diff_verts_enum dim_row_mat_less_card_I dim_submatrix(1) 
                    exist_index_in_submat dim_row_incidence_mat i_j(3-5)
                    le_neq_implies_less less(2) less_or_eq_imp_le not_less order_trans_rules(23)
                    pick_eq_iff_inf pick_mono_le 
                by (smt (verit, best))
              then have 25: "from_nat_into G (pick J t) = 
                         {Vs_enum_inv (pick I i), Vs_enum_inv (pick I j)}"
                using 6 22 23 24 
                by fastforce
              have 29: "(?u $ i) + (?u $ j) = 0"
              proof(cases "Vs_enum_inv (pick I i) \<in> R")
                case True
                have 26: "(?u $ i) = 1" 
                  by (simp add: True i_j(3))
                have "Vs_enum_inv (pick I j) \<notin> R" 
                  using True 25 22  insert_absorb  "23" "24" "27" bipartite_eqI bipartite_graph
                  by meson
                then have "?u $ j = -1" 
                  by (simp add: i_j(4))
                then show ?thesis 
                  using 26 by linarith
              next
                case False
                have 28: "(?u $ i) = - 1" 
                  by (simp add: False i_j(3))
                have "Vs_enum_inv (pick I j) \<in> R" 
                  using False 22 23 27 24  bipartite_eqI bipartite_graph 
                  by (smt (verit, ccfv_SIG) Vs_cases bipartite_commute vs_member_intro)
                then have "?u $ j = 1" 
                  by (simp add: i_j(4))
                then show ?thesis 
                  using 28 by linarith
              qed
              show "col B t \<bullet> ?u = 0" 
                using 29 30 by presburger
            qed
            then have "\<forall> t < dim_row B\<^sup>T. row B\<^sup>T t \<bullet> ?u = 0" 
              by (metis Matrix.col_transpose Matrix.transpose_transpose index_transpose_mat(2))
            then have 31: "B\<^sup>T *\<^sub>v ?u = 0\<^sub>v (dim_row B\<^sup>T)" 
              unfolding mult_mat_vec_def zero_vec_def
              by (metis (no_types, lifting) dim_vec eq_vecI index_transpose_mat(2) index_vec) 
            have 3: "\<exists>v. v \<in> carrier_vec (dim_row B\<^sup>T) \<and> 
                        v \<noteq> 0\<^sub>v (dim_row B\<^sup>T) \<and> B\<^sup>T *\<^sub>v v = 0\<^sub>v (dim_row B\<^sup>T)" 
              by (metis "1" 31 32 index_transpose_mat(2) vec_carrier)
            have 2: "B\<^sup>T \<in> carrier_mat (dim_row B) (dim_row B)" using 1 
              by auto
            then have "det B\<^sup>T = 0" 
              using det_0_iff_vec_prod_zero[OF 2] using 3 1
              by (metis index_transpose_mat(2))
            then have "det B = 0" 
              by (metis "2" Determinant.det_transpose Matrix.transpose_transpose)
            then show ?thesis 
              by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma is_bipartite_tot_unimod: "gram_schmidt_floor.tot_unimodular incidence_matrix" 
proof -
  have "(\<forall> B. (\<exists> I J. submatrix (incidence_matrix) I J = B) \<longrightarrow> det B \<in> {-1, 0, 1})"
    by (meson is_bipartite_submatrix_det_unimod)
  then show ?thesis
    using gram_schmidt_floor.tot_unimodular_def by blast
qed

lemma matching_polyh_int:
  shows "gram_schmidt_floor.int_polyh (card G) 
            (gram_schmidt_floor.pos_polyhedron (card G) incidence_matrix (1\<^sub>v (card (Vs G))))"
proof -
  have 1:"1\<^sub>v (card (Vs G)) \<in> \<int>\<^sub>v" 
    using gram_schmidt.one_vec_int by blast
  have 2:"(incidence_matrix) \<in> carrier_mat (card (Vs G)) (card G)" 
    using dim_col_incidence_mat dim_row_incidence_mat by blast
  then show "gram_schmidt_floor.int_polyh (card G) 
            (gram_schmidt_floor.pos_polyhedron (card G) (incidence_matrix) (1\<^sub>v (card (Vs G))))"
    using gram_schmidt_floor.tot_unimod_then_int_polyhedron[OF 2 is_bipartite_tot_unimod] 
    using "1" one_carrier_vec by blast
qed




lemma perfect_matching_polyhedron_integral:
  shows "gram_schmidt_floor.int_polyh (card G) 
            (gram_schmidt_floor.perfect_matching_polyhedron (card G) 
        incidence_matrix (1\<^sub>v (card (Vs G))))" 
proof -
  have "gram_schmidt_floor.int_polyh (card G) 
            (gram_schmidt_floor.pos_polyhedron (card G) incidence_matrix (1\<^sub>v (card (Vs G))))"
    by (metis matching_polyh_int)
  have "\<forall> F. gram_schmidt.face (card G) (gram_schmidt_floor.pos_polyhedron (card G) incidence_matrix (1\<^sub>v (card (Vs G)))) F
           \<longrightarrow> gram_schmidt_floor.int_polyh (card G) F"
  proof safe
    fix F
    assume asm: "gram_schmidt.face (card G) (gram_schmidt_floor.pos_polyhedron (card G) incidence_matrix (1\<^sub>v (card (Vs G)))) F" 
    have "gram_schmidt_floor.pos_polyhedron (card G) incidence_matrix (1\<^sub>v (card (Vs G))) = 
                  gram_schmidt.polyhedron (card G) (incidence_matrix @\<^sub>r - 1\<^sub>m (card G))
           ((1\<^sub>v (card (Vs G))) @\<^sub>v 0\<^sub>v (card G))" 
      using gram_schmidt_floor.pos_polyh_is_polyh  one_carrier_vec
      by (metis incidence_matrix_carrier_mat n_def)
    have 1:"incidence_matrix @\<^sub>r - 1\<^sub>m (card G) \<in> \<int>\<^sub>m" 
      using is_bipartite_tot_unimod dim_col_incidence_mat
            gram_schmidt_floor.tot_unimod_append_minus_one 
            gram_schmidt_floor.totally_unimod_mat_int carrier_mat_triv 
      by (metis carrier_mat_triv)

    have 2: "(1\<^sub>v (card (Vs G))) @\<^sub>v 0\<^sub>v (card G) \<in> \<int>\<^sub>v" 
      by (simp add: gram_schmidt.append_int_vec_is_int carrier_dim_vec gram_schmidt.one_vec_int gram_schmidt.zero_vec_is_int)
    have 3: "gram_schmidt_floor.int_polyh (card G) (gram_schmidt.polyhedron (card G)
       (incidence_matrix @\<^sub>r - 1\<^sub>m (card G)) ((1\<^sub>v (card (Vs G))) @\<^sub>v 0\<^sub>v (card G)))" 
      using \<open>gram_schmidt_floor.int_polyh (card G) (gram_schmidt_floor.pos_polyhedron (card G) incidence_matrix (1\<^sub>v (card (Vs G))))\<close>
            \<open>gram_schmidt_floor.pos_polyhedron (card G) incidence_matrix (1\<^sub>v (card (Vs G))) = gram_schmidt.polyhedron (card G) (incidence_matrix  @\<^sub>r - 1\<^sub>m (card G)) (1\<^sub>v (card (Vs G)) @\<^sub>v 0\<^sub>v (card G))\<close> by force
    have 4: "gram_schmidt.face (card G) (gram_schmidt.polyhedron (card G) (incidence_matrix @\<^sub>r - 1\<^sub>m (card G))
           ((1\<^sub>v (card (Vs G))) @\<^sub>v 0\<^sub>v (card G))) F" 
      using asm \<open>gram_schmidt_floor.pos_polyhedron (card G) incidence_matrix (1\<^sub>v (card (Vs G))) = gram_schmidt.polyhedron (card G) (incidence_matrix @\<^sub>r - 1\<^sub>m (card G)) (1\<^sub>v (card (Vs G)) @\<^sub>v 0\<^sub>v (card G))\<close> by force
    have 5: "incidence_matrix @\<^sub>r - 1\<^sub>m (card G) \<in> carrier_mat ((card (Vs G)) + (card G)) (card G)" 
      by (metis carrier_append_rows incidence_matrix_carrier_mat n_def
          one_carrier_mat uminus_carrier_mat)
    have 6: "((1\<^sub>v (card (Vs G))) @\<^sub>v 0\<^sub>v (card G)) \<in> carrier_vec ((card (Vs G)) + (card G))" 
      by simp
    show "gram_schmidt_floor.int_polyh (card G) F" 
      using gram_schmidt_floor.int_poly_face_int  5 6 3 4 1 2 
      by blast
  qed
  have 7: "incidence_matrix \<in> carrier_mat (card (Vs G)) m"
    unfolding incidence_matrix_def 
    by (metis n_def incidence_matrix_def incidence_matrix_carrier_mat)
                                                               
  show ?thesis using 
      gram_schmidt_floor.perfect_matching_polyhedron_face[of incidence_matrix "card (Vs G)" m " (1\<^sub>v (card (Vs G)))"]
    apply(simp add: 7)                            
  proof(cases "gram_schmidt_floor.perfect_matching_polyhedron
      m incidence_matrix
      (1\<^sub>v (card (Vs G))) \<noteq> {}")
    case True
    then show ?thesis 
      using   gram_schmidt_floor.perfect_matching_polyhedron_face
      using "7"
        \<open>\<forall>F. gram_schmidt.face m (gram_schmidt_floor.pos_polyhedron m incidence_matrix (1\<^sub>v (card (Vs G)))) F \<longrightarrow> gram_schmidt_floor.int_polyh m F\<close>
         one_carrier_vec by blast
  next
    case False
    have "gram_schmidt_floor.int_polyh (card G) {}"
      unfolding gram_schmidt_floor.int_polyh_def 
                gram_schmidt.integer_hull_def
      by (simp add: gram_schmidt.convex_hull_empty(1))
    then show ?thesis
      using False by auto
      
  qed                                                                            
qed                                                                                                                          
  
end
end
