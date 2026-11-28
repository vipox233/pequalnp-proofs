import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42582

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276813032 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x082880d8042a6da2#64 ++ 0x00105101b00854db#64 ++ 0x19e881f80c7ffffd#64 ++ 0x7833d103f018ffff#64 : BitVec 256),
   (0x2290362c319916d4#64 ++ 0x0845206c5863322d#64 ++ 0x6690fe3c73991ffb#64 ++ 0xd8cd21fc78e7323f#64 : BitVec 256),
   (0x85130b4582e1a358#64 ++ 0x050a26168b05c346#64 ++ 0x871f0fc783e1e3f7#64 ++ 0xef0e3e1f8f07c3c7#64 : BitVec 256),
   (0x581dd006dc01d860#64 ++ 0x12b03ba00db803b0#64 ++ 0xf81ff007fc01fc6f#64 ++ 0xb7f03fe00ff803f8#64 : BitVec 256),
   (0xf7c000036b540000#64 ++ 0x23ef800006d6a800#64 ++ 0xffe00007fffe005f#64 ++ 0xbbffc0000ffffc00#64 : BitVec 256),
   (0xffeeedb000000000#64 ++ 0x43ffdddb60000000#64 ++ 0xfffffff80000003f#64 ++ 0x47fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e881f80c7ffffd 0x7833d103f018ffff

def z1 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3c73991ffb 0xd8cd21fc78e7323f

def z2 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81ff007fc01fc6f 0xb7f03fe00ff803f8

def z3 : W := mkw 0x7a9dd006fd11d860 0x12f53ba00dfa23b0 0xfe9ff007ff99fc7f 0xbffd3fe00fff33f8

def z4 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc783e1e3f7 0xef0e3e1f8f07c3c7

def z5 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe00007fffe005f 0xbbffc0000ffffc00

def z6 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80000003f 0x47fffffff0000000

def z7 : W := mkw 0xffeeedb34a440000 0x63ffdddb66948800 0xfffffffb8c66003f 0x67fffffff718cc00

def z8 : W := mkw 0x2aaeedb000000000 0x40555ddb60000000 0x669ffff80000003b 0x44cd3ffff0000000

def z9 : W := mkw 0xd54000034a440000 0x23aa800006948800 0x996000038c660004 0x2332c0000718cc00

def z10 : W := mkw 0x580cd0025c005820 0x12b019a004b800b0 0x7800f0007c001c08 0x10f001e000f80038

def z11 : W := mkw 0x85020b4102e02318 0x050a04168205c046 0x07000fc003e00390 0x480e001f8007c007

def z12 : W := mkw 0x08288098040a4ca2 0x0010510130081499 0x18e080380c1e1c08 0x1031c10070183c38

def z13 : W := mkw 0x85130b0582c18258 0x050a26160b058304 0x86170e0783800002 0x870c2e1c0f070000

def z14 : W := mkw 0xa7c0262923dc0694 0x294f804c5247b80d 0x07e00e3803fe0390 0x480fc01c7007fc07

def z15 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x001ffff800000020 0x44003ffff0000000

def z16 : W := mkw 0xfffeffbc319916d4 0x4bfffdff7863322d 0xfffffffc73991fff 0xdffffffff8e7323f

def z17 : W := mkw 0x580cd0025c005820 0x12b019a004b800b0 0xf800f007fc001c4f 0xb3f001e00ff80038

def z18 : W := mkw 0xffeeedf8002a2582 0x43ffdddbf000544b 0xfffffff8007e03bf 0x4ffffffff000fc07

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0x19e000000c7e005d 0x3833c0000018fc00

def z20 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x861f0fc78381e3a2 0xc70c3e1f8f0703c7

def z21 : W := mkw 0x0011000480018040 0x0000220009000300 0x801f00078001e067 0xa7003e000f0003c0

def z22 : W := mkw 0x2280362831981694 0x0845006c5063302d 0x6680fe3873981f98 0x58cd01fc70e7303f

def z23 : W := mkw 0xffccd0037f545820 0x33ff99a006fea8b0 0xffe0f007fffe1c5f 0xbbffc1e00ffffc38

def z24 : W := mkw 0xa7c0000123540000 0x214f80000246a800 0x07e0000003fe0010 0x080fc0000007fc00

def z25 : W := mkw 0xffddd007ff55d860 0x33ffbba00ffeabb0 0xfffff007fffffc7f 0xbfffffe00ffffff8

def z26 : W := mkw 0xdd1fd947de61f968 0x17ba3fb28fbcc3f2 0xf91ff1c7fc61fc6f 0xb7f23fe38ff8c3f8

def z27 : W := mkw 0xdd6eedb000000000 0x43badddb60000000 0x997ffff800000024 0x4732fffff0000000

def z28 : W := mkw 0xdd1fdb47dee1fb78 0x17ba3fb68fbdc3f6 0xff1fffc7ffe1ffff 0xfffe3fff8fffc3ff

def z29 : W := mkw 0x00222db000000000 0x4000445b60000000 0x00000ff800000000 0x4000001ff0000000

def z30 : W := mkw 0x8d2a89d8042a6da2 0x011a5513b00854db 0x9fff8ff80c7fffff 0x7f3fff1ff018ffff

def z31 : W := mkw 0x00130b4582e1a358 0x040026168b05c346 0x001f0fc783e1e3e0 0xec003e1f8f07c3c7

def z32 : W := mkw 0xfffffdb6d8019040 0x53fffffb6db00320 0xfffffffff000003f 0xc7ffffffffe00000

def z33 : W := mkw 0x7aecf4b831181484 0x4af5d9e970623029 0x78e0f03870181c08 0x10f1c1e070e03038

def z34 : W := mkw 0x8502090000000000 0x010a041200000000 0x07000fc000000010 0x400e001f80000000

def z35 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xe01ff007f001fc22 0x87c03fe00fe003f8

def z36 : W := mkw 0x00000048042a6da2 0x00000000900854db 0x000000000c7fffc0 0x380000000018ffff

def z37 : W := mkw 0x2a9df62cb599def4 0x18553bec596b33bd 0x669ffe3c7399fffb 0xdccd3ffc78e733ff

def z38 : W := mkw 0xa7c000036b540000 0x214f800006d6a800 0x07e00007fffe0050 0xb80fc0000ffffc00

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x19e000000000001d 0x0033c00000000000

def z40 : W := mkw 0x000000036b540000 0x2000000006d6a800 0x00000007f3800000 0x800000000fe70000

def z41 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xfffffffffffe007f 0xfffffffffffffc00

def z42 : W := mkw 0xffeeedf8042a6da2 0x43ffdddbf00854db 0xfffffff80c7fffff 0x7ffffffff018ffff

def z43 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000047000004b 0x90c0000008e00000

def z44 : W := mkw 0x0011124db3f9b7dc 0x0c0022249b67f36f 0x00000007f3f9ffc0 0xb80000000fe7f3ff

def z45 : W := mkw 0x001100448021a140 0x0000220089004342 0x811f01c78061e3f7 0xef023e038f00c3c7

def z46 : W := mkw 0x00200098000a0482 0x0000400130001409 0x00e00038001e0000 0x0001c00070003c00

def z47 : W := mkw 0x8d3b8bdd86ebeffa 0x051a7717bb0dd7df 0x9fff8fff8fffffff 0xff3fff1fff1fffff

def z48 : W := mkw 0x8510020502c10250 0x010a20040a058204 0x87100e0783e103f7 0xeb0e201c0f07c207

def z49 : W := mkw 0x002000d8002a2582 0x00004001b000544b 0x01e001f8007e0390 0x4803c003f000fc07

def z50 : W := mkw 0xfffffdb6dc01d860 0x53fffffb6db803b0 0xfffffffffc01fc7f 0xf7fffffffff803f8

def z51 : W := mkw 0xffddd006dc01d860 0x13ffbba00db803b0 0xfffff007fc01fc7f 0xb7ffffe00ff803f8

def z52 : W := mkw 0x0000000800080480 0x0000000010001009 0x0080803800191ff9 0x580101007000323f

def z53 : W := mkw 0x2280262821980694 0x0845004c5043300d 0x06800e3803980390 0x480d001c70073007

def z54 : W := mkw 0x7a9df62efd99def4 0x1af53bec5dfb33bd 0xfe9ffe3fff99ffff 0xfffd3ffc7fff33ff

def z55 : W := mkw 0x2280242000000000 0x0045004840000000 0x6080f03800000008 0x00c101e070000000

def z56 : W := mkw 0x2291362cb19996d4 0x0845226c5963332d 0xe69ffe3ff399ffff 0xffcd3ffc7fe733ff

def z57 : W := mkw 0x002000d000222102 0x00004001a0004442 0x016001c000660000 0x0002c0038000cc00

def z58 : W := mkw 0x0000000000000000 0x0000000000000000 0x000800000001e065 0x20001000000003c0

def z59 : W := mkw 0x50155006d8019040 0x12a02aa00db00320 0xe0177007f0000002 0x87c02ee00fe00000

def z60 : W := mkw 0x0828809000000000 0x0010510120000000 0x19e881f80000003d 0x4033d103f0000000

def z61 : W := mkw 0xf7c66d2000000000 0x43ef8cda40000000 0xe6177e0000000002 0x07cc2efc00000000

def z62 : W := mkw 0xffdffd26dc01d860 0x53ffbffa4db803b0 0xfe1ffe07fc01fc6f 0xb7fc3ffc0ff803f8

def z63 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0x9fe000038ffe0014 0x2b3fc000071ffc00

def z64 : W := mkw 0x2280242821180484 0x0845004850423009 0x0080003800180000 0x0001000070003000

def z65 : W := mkw 0x580cc0024c004820 0x12b0198004980090 0x180000000c000000 0x0030000000180000

def z66 : W := mkw 0xa7e22db000000000 0x414fc45b60000000 0x07e00ff800000010 0x400fc01ff0000000

def z67 : W := mkw 0x083feff480a1a358 0x44107fdfe9014346 0x001ffff80001e3a0 0x44003ffff00003c7

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000800000011c69 0x1000010000000238

def z69 : W := mkw 0x0000004000202100 0x0000000080004042 0x010801c00061e3f5 0x680210038000c3c7

def z70 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xe61ffff800000022 0x47cc3ffff0000000

def z71 : W := mkw 0x0010362c108916d4 0x0800206c5821122d 0x0010fe3800011fa0 0x400021fc7000023f

def z72 : W := mkw 0x2280000021100000 0x0045000000422000 0x668000047398005b 0x98cd000008e73000

def z73 : W := mkw 0x8500000102400000 0x010a000002048000 0x8700000783e00057 0xab0e00000f07c000

def z74 : W := mkw 0xffffeff582e1a358 0x47ffffdfeb05c346 0xffffffff83e1e3ff 0xefffffffff07c3c7

def z75 : W := mkw 0x082880db6f7e6da2 0x20105101b6defcdb 0x19e881fffffffffd 0xf833d103ffffffff

def z76 : W := mkw 0xffe880db6f7e6da2 0x23ffd101b6defcdb 0xffe881ffffffffff 0xfbffd103ffffffff

def z77 : W := mkw 0x581dd006d8019040 0x12b03ba00db00320 0xf81ff007f000002f 0x87f03fe00fe00000

def z78 : W := mkw 0xf7d33f6ffbfdb7dc 0x2fefa67edff7fb6f 0xffffffffffffffff 0xffffffffffffffff

def z79 : W := mkw 0x0011000480018040 0x0000220009000300 0x000000078001e040 0xa00000000f0003c0

def z80 : W := mkw 0xa7f23fbc319916d4 0x494fe47f7863322d 0x67f0fffc73991ffb 0xd8cfe1fff8e7323f

def z81 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z82 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xf9eff1f80000000c 0x07f3dfe3f0000000

def z83 : W := mkw 0x0000342810081484 0x0800006850201029 0x0000f03800001c00 0x000001e070000038

def z84 : W := mkw 0x0011024582e1a358 0x040022048b05c346 0x06100e0783e1e3f3 0xe80c201c0f07c3c7

def z85 : W := mkw 0x0010120c319916d4 0x080020241863322d 0x6010f00473991feb 0x98c021e008e7323f

def z86 : W := mkw 0xffeefdb831181484 0x4bffddfb70623029 0xfffffff870181c3f 0x57fffffff0e03038

def z87 : W := mkw 0x2280242021100000 0x0045004840422000 0x6690fe3c7398007b 0xd8cd21fc78e73000

def z88 : W := mkw 0x0000004004226922 0x00000000800844d2 0x000000000c66e000 0x200000000018cdc0

def z89 : W := mkw 0x583dd0dedc2bfde2 0x12b07ba1bdb857fb 0xf81ff1fffc01ffef 0xf7f03fe3fff803ff

def z90 : W := mkw 0xf7c66d236b540000 0x63ef8cda46d6a800 0xfff77e07fffe005f 0xbfffeefc0ffffc00

def z91 : W := mkw 0xdd6ec99000000000 0x43badd9320000000 0x9f7f0fc000000037 0x473efe1f80000000

def z92 : W := mkw 0x7295762ef99996d4 0x1ae52aec5df3332d 0xe697fe3ff3991ffb 0xdfcd2ffc7fe7323f

def z93 : W := mkw 0x850309418260a108 0x050a06128304c142 0x871f0fc38060e037 0x670e3e1f8700c1c0

def z94 : W := mkw 0x2280342831181484 0x0845006850623029 0x6080f03870191ff9 0x58c101e070e0323f

def z95 : W := mkw 0x0010020400810250 0x0000200408010204 0x06100e04038103f3 0xc80c201c08070207

def z96 : W := mkw 0x2280342831181484 0x0845006850623029 0x6080f03870181c08 0x10c101e070e03038

def z97 : W := mkw 0x581dc006cc01c860 0x12b03b800d980390 0x981f00078c01e067 0xa7303e000f1803c0

def z98 : W := mkw 0xd5530b47cae5a358 0x27aaa6168f95cb46 0x9f7f0fc78fe7e3f7 0xef3efe1f8f1fcfc7

def z99 : W := mkw 0x00130b4480a1a358 0x0400261689014346 0x001f0fc00001e3a0 0x44003e1f800003c7

def z100 : W := mkw 0x083b8bdc84abeffa 0x04107717b90957df 0x19ff8ff80c7ffffd 0x7c33ff1ff018ffff

def z101 : W := mkw 0x8d2eedb000000000 0x411a5ddb60000000 0x871ffff800000037 0x470e3ffff0000000

def z102 : W := mkw 0x2280242000000000 0x0045004840000000 0x06800e3800000010 0x400d001c70000000

def z103 : W := mkw 0x2ab8b6fc35bb7ff6 0x0855716df86b76ff 0x7ff8fffc7fffffff 0xf8fff1fff8ffffff

def z104 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xfee00007ff9e000a 0x93fdc0000fff3c00

def z105 : W := mkw 0x72c0000269140000 0x22e5800004d22800 0x79e000007c7e005d 0x38f3c00000f8fc00

def z106 : W := mkw 0x7ae8809a6d1e4ca2 0x22f5d10134da3c99 0x78e080387c1e1c08 0x10f1c10070f83c38

def z107 : W := mkw 0x583ffdb6dc01d860 0x52b07ffb6db803b0 0xf81ffffffc01fc6f 0xf7f03ffffff803f8

def z108 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x9fff0fc78fffe3ff 0xff3ffe1f8f1fffc7

def z109 : W := mkw 0x85020b4102e02318 0x050a04168205c046 0x87000fc783e003d7 0xeb0e001f8f07c007

def z110 : W := mkw 0x7aece4b000000000 0x42f5d9c960000000 0x79e8f1f80000003d 0x40f3d1e3f0000000

def z111 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xe6000007fffe0042 0xbbcc00000ffffc00

def z112 : W := mkw 0xf7c024236b540000 0x23ef804846d6a800 0xfff0fe3ffffe007f 0xfbffe1fc7ffffc00

def z113 : W := mkw 0xf7d30b47ebf5a358 0x27efa6168fd7eb46 0xffff0fc7ffffe3ff 0xfffffe1f8fffffc7

def z114 : W := mkw 0x0000000800080480 0x0000000010001009 0x0080803800181c08 0x1001010070003038

def z115 : W := mkw 0x580cc00000000000 0x02b0198000000000 0xf81ff0000000002f 0x07f03fe000000000

def z116 : W := mkw 0x0808800000000000 0x0010110000000000 0x180880000000002d 0x0030110000000000

def z117 : W := mkw 0xffeeedf8042a6da2 0x43ffdddbf00854db 0xfffffff80001ffbf 0x47fffffff00003ff

def z118 : W := mkw 0x2291362efd99def4 0x1845226c5dfb33bd 0x6690fe3fff99fffb 0xf8cd21fc7fff33ff

def z119 : W := mkw 0x00000048042a6da2 0x00000000900854db 0x19e000000c7fffdd 0x3833c0000018ffff

def z120 : W := mkw 0x50111006dc01d860 0x12a022200db803b0 0xf8000007fc01fc4f 0xb3f000000ff803f8

def z121 : W := mkw 0x0000004000202100 0x0000000080004042 0x010801c00060e004 0x200210038000c1c0

def z122 : W := mkw 0x850309418260a108 0x050a06128304c142 0x810f01c38061e3f5 0x6f021e038700c3c7

def z123 : W := mkw 0xa7930b45a3f1a358 0x054f26168b47e346 0xe79f0fc7f3f9e3ff 0xffcf3e1f8fe7f3c7

def z124 : W := mkw 0x000000036b540000 0x2000000006d6a800 0x19e00007fffe005d 0xb833c0000ffffc00

def z125 : W := mkw 0xffeeedb021100000 0x43ffdddb60422000 0xfffffffc7398007f 0xdffffffff8e73000

def z126 : W := mkw 0xfffffdb49401d860 0x53fffffb692803b0 0xfffffff80001fc3f 0x47fffffff00003f8

def z127 : W := mkw 0x72c0000269140000 0x22e5800004d22800 0x78e000007c1e0008 0x10f1c00000f83c00

def z128 : W := mkw 0xf7e000db6b7e2582 0x23efc001b6d6fc4b 0xffe001fffffe03df 0xfbffc003fffffc07

def z129 : W := mkw 0x0000004000202100 0x0000000080004042 0x000000000061e3c0 0x280000000000c3c7

def z130 : W := mkw 0xf7c66d2000000000 0x43ef8cda40000000 0xfff77e000000001f 0x07ffeefc00000000

def z131 : W := mkw 0x85120b0400810250 0x010a241608010204 0x871f0fc4038103f7 0xcf0e3e1f88070207

def z132 : W := mkw 0xdd0ec90000000000 0x03ba1d9200000000 0xff1fffc00000003f 0x47fe3fff80000000

def z133 : W := mkw 0x2290362431911254 0x0845206c48632224 0x66107e0473800002 0x80cc20fc08e70000

def z134 : W := mkw 0xf7c0342b7b5c1484 0x2bef806856f6b829 0xffe0f03ffffe1c5f 0xbbffc1e07ffffc38

def z135 : W := mkw 0xdd6880db4e6e6da2 0x23bad101b69cdcdb 0x99e881fb8c7ffffd 0x7b33d103f718ffff

def z136 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0x980f0007fc01fc44 0xb7301e000ff803f8

def z137 : W := mkw 0xa7822f6923f8279c 0x0d4f045ed247f04f 0x07800ff803f80390 0x480f001ff007f007

def z138 : W := mkw 0x2280242000000000 0x0045004840000000 0x6690fe380000003b 0x40cd21fc70000000

def z139 : W := mkw 0xd54000036b540000 0x23aa800006d6a800 0x99600007fffe0044 0xbb32c0000ffffc00

def z140 : W := mkw 0x0828809000000000 0x0010510120000000 0x000881f800000020 0x40001103f0000000

def z141 : W := mkw 0x2a98b62c35995ef4 0x0855316c586b32bd 0x7e98fe3c7f99ffff 0xf8fd31fc78ff33ff

def z142 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xe6000007f3800002 0x83cc00000fe70000

def z143 : W := mkw 0x7aece4b8040a4ca2 0x42f5d9c970081499 0x78e0f0380c1e1c08 0x10f1c1e070183c38

def z144 : W := mkw 0x580dc002cc00c820 0x12b01b8005980190 0x980f00038c00e004 0x27301e00071801c0

def z145 : W := mkw 0x2290262400810250 0x0045204c48010204 0x6690fe3c038103fb 0xc8cd21fc78070207

def z146 : W := mkw 0x2290262c219906d4 0x0845204c5843320d 0x06900e3c039903f3 0xc80d201c78073207

def z147 : W := mkw 0xd5430943ca64a108 0x27aa86128794c942 0x996f01c38c66e004 0x2732de038718cdc0

def z148 : W := mkw 0x000000036b540000 0x2000000006d6a800 0x00000007fffe0040 0xb80000000ffffc00

def z149 : W := mkw 0x2290366c31b937d4 0x0845206cd863726f 0x6798fffc73f9ffff 0xf8cf31fff8e7f3ff

def z150 : W := mkw 0x080dc0008400c820 0x10101b8001080190 0x000f00000000e000 0x04001e00000001c0

def z151 : W := mkw 0x5000000248000000 0x02a0000004900000 0x780000007c000008 0x10f0000000f80000

def z152 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x071f0fc003e1e3b0 0x4c0e3e1f8007c3c7

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x010801c000000035 0x4002100380000000

def z154 : W := mkw 0x0010100410011040 0x0000202008200220 0x6010f00470011c6b 0x90c021e008e00238

def z155 : W := mkw 0x00000048042a6da2 0x00000000900854db 0x008080380c7ffff9 0x780101007018ffff

def z156 : W := mkw 0xffccc00000000000 0x03ff998000000000 0xfffff0000000003f 0x07ffffe000000000

def z157 : W := mkw 0x002000d8002a2582 0x00004001b000544b 0x19e001f80c7e03dd 0x7833c003f018fc07

def z158 : W := mkw 0x0011024582e1a358 0x040022048b05c346 0x0000000783e1e3c0 0xa80000000f07c3c7

def z159 : W := mkw 0x082880d004226922 0x00105101a00844d2 0x196801c00c66e004 0x2032d0038018cdc0

def z160 : W := mkw 0xfffb8bdfefffeffa 0x27fff717bfdfffdf 0xffff8fffffffffff 0xffffff1fffffffff

def z161 : W := mkw 0x0011020582c18258 0x040022040b058304 0x0000000783800000 0x800000000f070000

def z162 : W := mkw 0xffceed2000000000 0x43ff9dda40000000 0xfe1ffe000000002f 0x07fc3ffc00000000

def z163 : W := mkw 0x581dd206dc81da70 0x12b03ba40db903b4 0xfe1ffe07ff81ffff 0xfffc3ffc0fff03ff

def z164 : W := mkw 0xfffffffdb3f9b7dc 0x4ffffffffb67f36f 0xfffffffff3f9ffff 0xffffffffffe7f3ff

def z165 : W := mkw 0xffffedb480018040 0x43ffffdb69000300 0xffffffff8001e07f 0xe7ffffffff0003c0

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000103f1 0x4800000000000207

def z167 : W := mkw 0xafbbbffdb7fbfffe 0x0d5f777ffb6ff7ff 0xffffffffffffffff 0xffffffffffffffff

def z168 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x19fffff80000003d 0x4433fffff0000000

def z169 : W := mkw 0xdd1fcb47cee1eb78 0x17ba3f968f9dc3d6 0x9f1f0fc78fe1e3f7 0xef3e3e1f8f1fc3c7

def z170 : W := mkw 0x7aece4b000000000 0x42f5d9c960000000 0x78e0f03800000008 0x00f1c1e070000000

def z171 : W := mkw 0x2aa8b4b8351a5ca6 0x08555169706a34b9 0x78e0f0387c1e1c08 0x10f1c1e070f83c38

def z172 : W := mkw 0x581dd0049401d860 0x12b03ba0092803b0 0xf81ff0000001fc2f 0x07f03fe0000003f8

def z173 : W := mkw 0x082ce4b000000000 0x401059c960000000 0x0000f03800000000 0x000001e070000000

def z174 : W := mkw 0xa7e22df8002a2582 0x414fc45bf000544b 0x07e00ff8007e0390 0x480fc01ff000fc07

def z175 : W := mkw 0xf7e22db36b540000 0x63efc45b66d6a800 0xffe00ffffffe005f 0xfbffc01ffffffc00

def z176 : W := mkw 0xffcdc003ef54c820 0x33ff9b8007dea990 0xffef0007fffee05f 0xbfffde000ffffdc0

def z177 : W := mkw 0xa7e22db000000000 0x414fc45b60000000 0x87ff0ff800000037 0x470ffe1ff0000000

def z178 : W := mkw 0x50110006c8018040 0x02a022000d900300 0xf81f0007fc01e06f 0xb7f03e000ff803c0

def z179 : W := mkw 0xd5175b47dae1b358 0x17aa2eb68fb5c366 0xe71f7fc7f3e1e3f7 0xefce3eff8fe7c3c7

def z180 : W := mkw 0x081fdb4494a1fb78 0x14103fb6892943f6 0x001fffc00001ffa0 0x44003fff800003ff

def z181 : W := mkw 0x580cc00248000000 0x02b0198004900000 0xf81ff007fc00006f 0xb7f03fe00ff80000

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x01e00000007e0010 0x0803c0000000fc00

def z183 : W := mkw 0x00000048002a2582 0x000000009000544b 0x00000000007e0380 0x080000000000fc07

def z184 : W := mkw 0xffeec99000000000 0x43ffdd9320000000 0xffef01c00000001f 0x07ffde0380000000

def z185 : W := mkw 0x2280342031101004 0x0845006840622020 0x6000700070000000 0x00c000e000e00000

def z186 : W := mkw 0x0808800004004820 0x0010110000080090 0x180880000c01fc6d 0x30301100001803f8

def z187 : W := mkw 0x580880024c004820 0x02b0110004980090 0xf8088007fc01fc6f 0xb3f011000ff803f8

def z188 : W := mkw 0xffffffbefd99def4 0x5bffffff7dfb33bd 0xffffffffff99ffff 0xffffffffffff33ff

def z189 : W := mkw 0x083ffdb49401d860 0x50107ffb692803b0 0x001ffff80001fc20 0x44003ffff00003f8

def z190 : W := mkw 0x8502090000000000 0x010a041200000000 0x871f0fc000000037 0x470e3e1f80000000

def z191 : W := mkw 0x0000000000000000 0x0000000000000000 0x801f000000000027 0x07003e0000000000

def z192 : W := mkw 0x8511000582418040 0x010a22000b048300 0x871f000783e1e077 0xaf0e3e000f07c3c0

def z193 : W := mkw 0x85020b4102e02318 0x050a04168205c046 0x871f0fc003e003b7 0x4f0e3e1f8007c007

def z194 : W := mkw 0x0010120c319916d4 0x080020241863322d 0x06100e0473991ff3 0xd80c201c08e7323f

def z195 : W := mkw 0x0838b6fc14ab7ff6 0x0810716df82956ff 0x19f8fff80c7ffffd 0x7833f1fff018ffff

def z196 : W := mkw 0x083892dc35bb7ff6 0x08107125b86b76ff 0x19e881fc7ffffffd 0xf833d103f8ffffff

def z197 : W := mkw 0x582eedb000000000 0x42b05ddb60000000 0xf81ffff80000002f 0x47f03ffff0000000

def z198 : W := mkw 0x85330bdd82eba7da 0x050a6617bb05d74f 0x87ff0fff83ffe3f7 0xef0ffe1fff07ffc7

def z199 : W := mkw 0x0011000480018040 0x0000220009000300 0x8017000780000002 0x87002e000f000000

def z200 : W := mkw 0xffdfdb47fff5fb78 0x37ffbfb68fffebf6 0xffffffc7ffffffff 0xffffffff8fffffff

def z201 : W := mkw 0xd5130b47cae1a358 0x07aa26168f95c346 0xff1f0fc7ffe1e3ff 0xfffe3e1f8fffc3c7

def z202 : W := mkw 0x8502090000000000 0x010a041200000000 0x86170e0000000002 0x070c2e1c00000000

def z203 : W := mkw 0xdd6ec99000000000 0x43badd9320000000 0x996f01c000000004 0x0732de0380000000

def z204 : W := mkw 0x0000000800080480 0x0000000010001009 0x0080003800180390 0x4801000070003007

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x196000000c660004 0x2032c0000018cc00

def z206 : W := mkw 0xf7d0362f7bdd16d4 0x2befa06c5ef7ba2d 0xfff0fe3fffff1fff 0xfbffe1fc7ffffe3f

def z207 : W := mkw 0x7280000269100000 0x02e5000004d22000 0xfe800007ff98005f 0xbbfd00000fff3000

def z208 : W := mkw 0xa7933f6db3f9b7dc 0x0d4f267edb67f36f 0xe79ffffff3f9ffff 0xffcf3fffffe7f3ff

def z209 : W := mkw 0x581dd007ff55d860 0x32b03ba00ffeabb0 0xf81ff007fffffc6f 0xbff03fe00ffffff8

def z210 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x66107e0473991fc2 0x98cc20fc08e7323f

def z211 : W := mkw 0x0000024102e02318 0x040000048205c046 0x0000000003e00380 0x080000000007c007

def z212 : W := mkw 0x7ae880da6d3e6da2 0x22f5d101b4da7cdb 0x79e881f87c7ffffd 0x78f3d103f0f8ffff

def z213 : W := mkw 0x582dc0dacc2aeda2 0x12b05b81b59855db 0x99ef81fb8c7ffffd 0x7f33df03f718ffff

def z214 : W := mkw 0xdd0fc943ce60e928 0x17ba1f92879cc1d2 0x990f01c38c60e004 0x27321e038718c1c0

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000c7e0040 0x380000000018fc00

def z216 : W := mkw 0x8500000102400000 0x010a000002048000 0x0700000003e00010 0x080e00000007c000

def z217 : W := mkw 0xffeeedb269140000 0x63ffdddb64d22800 0xfffffff87c1e003f 0x57fffffff0f83c00

def z218 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e881f80001ffbd 0x4033d103f00003ff

def z219 : W := mkw 0xf7e66db000000000 0x43efccdb60000000 0xe7f77ff800000012 0x47cfeefff0000000

def z220 : W := mkw 0x581dd046dc21f960 0x12b03ba08db843f2 0xf91ff1c7fc61ffff 0xfff23fe38ff8c3ff

def z221 : W := mkw 0xf7d0362f7bdd16d4 0x2befa06c5ef7ba2d 0xe690fe3ff3991ffb 0xdbcd21fc7fe7323f

def z222 : W := mkw 0x580dd002dc00d820 0x12b01ba005b801b0 0xf80ff003fc00fc0c 0x37f01fe007f801f8

def z223 : W := mkw 0xa7822d2000000000 0x014f045a40000000 0xe79ffff80000003f 0x47cf3ffff0000000

def z224 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0x7fe0fff800000018 0x40ffc1fff0000000

def z225 : W := mkw 0x5004500258001000 0x12a008a004b00020 0x6000700070000000 0x00c000e000e00000

def z226 : W := mkw 0xa7e22ff102e02318 0x454fc45fe205c046 0x07e00ff803e00390 0x480fc01ff007c007

def z227 : W := mkw 0xfffeffbf7bdd16d4 0x6bfffdff7ef7ba2d 0xffffffffffff1fff 0xfffffffffffffe3f

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x18e000000c1e0008 0x1031c00000183c00

def z229 : W := mkw 0x580cd0025c005820 0x12b019a004b800b0 0x7808f0007c01fc6d 0x30f011e000f803f8

def z230 : W := mkw 0x8d3b8bdd86ebeffa 0x051a7717bb0dd7df 0x871f8fff83e1fff7 0xef0e3f1fff07c3ff

def z231 : W := mkw 0x72c0342a791c1484 0x2ae5806854f23829 0x78e0f0387c1e1c08 0x10f1c1e070f83c38

def z232 : W := mkw 0x582880da4c2a6da2 0x02b05101b49854db 0xf9e881fffc7fffff 0xfbf3d103fff8ffff

def z233 : W := mkw 0xafe880d9277e6da2 0x215fd101b24efcdb 0x1fe881f80ffffffd 0x783fd103f01fffff

def z234 : W := mkw 0xf7c0000000000000 0x03ef800000000000 0xffe000000000001f 0x03ffc00000000000

def z235 : W := mkw 0x581dd04edc2bfde2 0x12b03ba09db857fb 0xf81ff007fc7fffef 0xbff03fe00ff8ffff

def z236 : W := mkw 0x0011024582e1a358 0x040022048b05c346 0x010801c783e1e3f5 0xe80210038f07c3c7

def z237 : W := mkw 0x2aa880d8253a6da2 0x00555101b04a74db 0x7fe881fc7fffffff 0xf8ffd103f8ffffff

def z238 : W := mkw 0x850309418260a108 0x050a06128304c142 0x870f01c783e0e057 0xaf0e1e038f07c1c0

def z239 : W := mkw 0xf7d30b07ebd58258 0x27efa6160fd7ab04 0xe6170e07f3800002 0x87cc2e1c0fe70000

def z240 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x000881f80001ffa0 0x40001103f00003ff

def z241 : W := mkw 0x0001000080008000 0x0000020001000100 0x800f00038000e004 0x27001e00070001c0

def z242 : W := mkw 0xd54000034a440000 0x23aa800006948800 0x8000000380000000 0x0300000007000000

def z243 : W := mkw 0x5000000248000000 0x02a0000004900000 0xf9e00007fc7e005f 0xbbf3c0000ff8fc00

def z244 : W := mkw 0x50155006d8019040 0x12a02aa00db00320 0xf8177007fc00004f 0xb7f02ee00ff80000

def z245 : W := mkw 0xdd6ec99000000000 0x43badd9320000000 0xf97ff1c00000002f 0x07f2ffe380000000

def z246 : W := mkw 0xafeeedb000000000 0x415fdddb60000000 0x07fffff800000030 0x440ffffff0000000

def z247 : W := mkw 0xa7e22db123540000 0x614fc45b6246a800 0x07e00ff803fe0010 0x480fc01ff007fc00

def z248 : W := mkw 0x00066d2000000000 0x40000cda40000000 0x00177e0000000000 0x04002efc00000000

def z249 : W := mkw 0xd546490000000000 0x43aa8c9200000000 0x8007000000000000 0x07000e0000000000

def z250 : W := mkw 0x72c0000269140000 0x22e5800004d22800 0x6000000070000000 0x00c0000000e00000

def z251 : W := mkw 0xa7e22fb821980694 0x494fc45f7043300d 0x07e00ff803980390 0x480fc01ff0073007

def z252 : W := mkw 0x5000000248000000 0x02a0000004900000 0xf8000007fc00004f 0xb3f000000ff80000

def z253 : W := mkw 0xf7c0000248000000 0x03ef800004900000 0xffe00007fc00005f 0xb3ffc0000ff80000

def z254 : W := mkw 0x00020b4000a02318 0x0400041680014046 0x00000fc000000380 0x4000001f80000007

def z255 : W := mkw 0x583dd096dc01d860 0x12b07ba12db803b0 0xf9fff1fffc01fc7f 0xf7f3ffe3fff803f8

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000000600055 0x280200000000c000

def z257 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x7ff0fe3c7fff1fff 0xf8ffe1fc78fffe3f

def z258 : W := mkw 0x580cc00000000000 0x02b0198000000000 0x7800f00000000008 0x00f001e000000000

def z259 : W := mkw 0x850309418260a108 0x050a06128304c142 0x810f01c38060e004 0x27021e038700c1c0

def z260 : W := mkw 0x7aece4b000000000 0x42f5d9c960000000 0xf8fff0380000002f 0x07f1ffe070000000

def z261 : W := mkw 0x2290362431911254 0x0845206c48632224 0x66107e04738103f3 0xc8cc20fc08e70207

def z262 : W := mkw 0xffffefb582c18258 0x47ffffdf6b058304 0xffffffff8380003f 0xc7ffffffff070000

def z263 : W := mkw 0xf7c0000102400000 0x03ef800002048000 0xffe0000783e0005f 0xabffc0000f07c000

def z264 : W := mkw 0xffeeedf004226922 0x43ffdddbe00844d2 0xfffffff80c66e03f 0x67fffffff018cdc0

def z265 : W := mkw 0x0010120c108916d4 0x080020241821122d 0x0000000000011f80 0x000000000000023f

def z266 : W := mkw 0x2290120c319916d4 0x084520241863322d 0x6680000473991fdb 0x98cd000008e7323f

def z267 : W := mkw 0x583dd0dedc2bfde2 0x12b07ba1bdb857fb 0xf9fff1fffc7fffff 0xfff3ffe3fff8ffff

def z268 : W := mkw 0xf7c0000000000000 0x03ef800000000000 0xe600000000000002 0x03cc000000000000

def z269 : W := mkw 0xf7c0262b6bdc0694 0x2bef804c56d7b80d 0xffe00e3ffffe03df 0xfbffc01c7ffffc07

def z270 : W := mkw 0x0010120c319916d4 0x080020241863322d 0x0000000473991fc0 0x9800000008e7323f

def z271 : W := mkw 0x0011024582e1a358 0x040022048b05c346 0x801f000783e1e3e7 0xaf003e000f07c3c7

def z272 : W := mkw 0xf7d76f2582c18258 0x47efaede4b058304 0xe6177e0783800002 0x87cc2efc0f070000

def z273 : W := mkw 0x50155006d8019040 0x12a02aa00db00320 0xe017f007f0011c6b 0x97c02fe00fe00238

def z274 : W := mkw 0xa7933f25b3d1925c 0x0d4f267e4b67a324 0xe6177e07f3800002 0x87cc2efc0fe70000

def z275 : W := mkw 0x0000000800080480 0x0000000010001009 0x19e080380c7f1ffd 0x7833c1007018fe3f

def z276 : W := mkw 0x000000034a440000 0x2000000006948800 0x000000038c660000 0x200000000718cc00

def z277 : W := mkw 0xf7d010077b551040 0x23efa0200ef6aa20 0xfff0f007ffff1c7f 0xbbffe1e00ffffe38

def z278 : W := mkw 0xffeefdb25c005820 0x53ffddfb64b800b0 0xfffffff87c001c3f 0x57fffffff0f80038

def z279 : W := mkw 0x7aecf4b25c005820 0x52f5d9e964b800b0 0x78e0f0387c001c08 0x10f1c1e070f80038

def z280 : W := mkw 0x00111006dc01d860 0x100022200db803b0 0x6010f007fc01fc6b 0xb0c021e00ff803f8

def z281 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x07000fc783e1e3d0 0xe80e001f8f07c3c7

def z282 : W := mkw 0x581dc00480018040 0x02b03b8009000300 0xf81ff0078001e06f 0xa7f03fe00f0003c0

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000000180059 0x1801000000003000

def z284 : W := mkw 0x72c4642000000000 0x42e588c840000000 0x6000700000000000 0x00c000e000000000

def z285 : W := mkw 0xf7d30b07ebd58258 0x27efa6160fd7ab04 0xfff70e07fffe005f 0xbfffee1c0ffffc00

def z286 : W := mkw 0x081dd0049401d860 0x10103ba0092803b0 0x001ff0000001fc20 0x04003fe0000003f8

def z287 : W := mkw 0xffc880036f544820 0x23ff910006dea890 0xffe88007fffffc7f 0xbbffd1000ffffff8

def z288 : W := mkw 0x08199006dc01d860 0x101033200db803b0 0x18088007fc01fc6d 0xb03011000ff803f8

def z289 : W := mkw 0x00130b4480a1a358 0x0400261689014346 0x061f0fc40381e3f3 0xcc0c3e1f880703c7

def z290 : W := mkw 0x851309458261a148 0x050a26128b04c342 0x811f01c78061e067 0xa7023e038f00c3c0

def z291 : W := mkw 0x581cd00410011040 0x02b039a008200220 0xf81ff00470011c6f 0x97f03fe008e00238

def z292 : W := mkw 0xffeeedb248000000 0x43ffdddb64900000 0xfffffffffc00007f 0xf7fffffffff80000

def z293 : W := mkw 0x85131b47dee1fb78 0x150a26368fbdc3f6 0x871f0fc7ffe1fff7 0xff0e3e1f8fffc3ff

def z294 : W := mkw 0x2280342831181484 0x0845006850623029 0x6690fe3870181c3b 0x50cd21fc70e03038

def z295 : W := mkw 0x85130b47ebf5a358 0x250a26168fd7eb46 0x871f0fc7ffffe3f7 0xff0e3e1f8fffffc7

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000000c00004d 0x3030000000180000

def z297 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6610fe3c73811fa2 0xc0cc21fc78e7023f

def z298 : W := mkw 0xf7d30b47ebf5a358 0x27efa6168fd7eb46 0xe71f0fc7f3e1e3f7 0xefce3e1f8fe7c3c7

def z299 : W := mkw 0x2ab8b6fc35bb7ff6 0x0855716df86b76ff 0x6698fffc7399fffb 0xd8cd31fff8e733ff

def z300 : W := mkw 0x8502094000202100 0x010a041280004042 0x871f0fc00061e3f7 0x6f0e3e1f8000c3c7

def z301 : W := mkw 0x85030b4182e0a318 0x050a06168305c146 0x870f0fc383e0e394 0x6f0e1e1f8707c1c7

def z302 : W := mkw 0x00130b4480a1a358 0x0400261689014346 0x801f0fc78001e3e7 0xe7003e1f8f0003c7

def z303 : W := mkw 0x0000004000202100 0x0000000080004042 0x19e801c00c7fe3fd 0x7833d0038018ffc7

def z304 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080803800000039 0x4001010070000000

def z305 : W := mkw 0x85130b0582c18258 0x050a26160b058304 0x87170e0783e00057 0xaf0e2e1c0f07c000

def z306 : W := mkw 0xfffeefb400810250 0x43fffddf68010204 0xfffffffc038103ff 0xcffffffff8070207

def z307 : W := mkw 0x85131b4592e1b358 0x050a26368b25c366 0xe71fffc7f3e1ffff 0xffce3fff8fe7c3ff

def z308 : W := mkw 0x0011000480018040 0x0000220009000300 0x001f00000001e020 0x04003e00000003c0

def z309 : W := mkw 0x080cc00000000000 0x0010198000000000 0x001ff00000000020 0x04003fe000000000

def z310 : W := mkw 0x0000000123540000 0x200000000246a800 0x0000000003fe0000 0x080000000007fc00

def z311 : W := mkw 0x7aeeedb000000000 0x42f5dddb60000000 0x78fffff800000028 0x44f1fffff0000000

def z312 : W := mkw 0x0010020c008906d0 0x000020041801120d 0x06908e3c03991ffb 0xd80d211c7807323f

def z313 : W := mkw 0x8502094102602108 0x050a04128204c042 0x010001c000600000 0x000200038000c000

def z314 : W := mkw 0xa7933f65b3f1b35c 0x0d4f267ecb67e366 0xe71f7fc7f3e1e3f7 0xefce3eff8fe7c3c7

def z315 : W := mkw 0x0838b6fc14ab7ff6 0x0810716df82956ff 0x0018fff80001ffa0 0x400031fff00003ff

def z316 : W := mkw 0xf7c0000000000000 0x03ef800000000000 0xffe000000c7e005f 0x3bffc0000018fc00

def z317 : W := mkw 0x22c0000021140000 0x2045800000422800 0x00e00000001e0000 0x0001c00000003c00

def z318 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6090fe3870191fa8 0x50c121fc70e0323f

def z319 : W := mkw 0x8500000000000000 0x010a000000000000 0x8700000000000017 0x030e000000000000

def z320 : W := mkw 0x50155006dc01d860 0x12a02aa00db803b0 0xe0177007fc01fc42 0xb7c02ee00ff803f8

def z321 : W := mkw 0xa7923f6d33f937dc 0x0d4f247eda67f26f 0x6790fffc73f91ffb 0xd8cf21fff8e7f23f

def z322 : W := mkw 0x00111006dc01d860 0x100022200db803b0 0x00000007fc01fc40 0xb00000000ff803f8

def z323 : W := mkw 0xf7d76f6582e1a358 0x47efaedecb05c346 0xe71f7fc783e1e3f7 0xefce3eff8f07c3c7

def z324 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x196801c00c7fffc4 0x3832d0038018ffff

def z325 : W := mkw 0x08288098040a4ca2 0x0010510130081499 0x0000803800001c00 0x0000010070000038

def z326 : W := mkw 0xd5175b07dac19258 0x17aa2eb60fb58324 0xe6177e07f3800002 0x87cc2efc0fe70000

def z327 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x01e881f8007fffb0 0x4803d103f000ffff

def z328 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xfffffffff380003f 0xc7ffffffffe70000

def z329 : W := mkw 0x0828809800080480 0x0010510130001009 0x19e881f800191ffd 0x5833d103f000323f

def z330 : W := mkw 0xf7d30b4582e1a358 0x07efa6168b05c346 0xffff0fc783e1e3ff 0xeffffe1f8f07c3c7

def z331 : W := mkw 0x082ec99000000000 0x40105d9320000000 0x000f01c000000000 0x04001e0380000000

def z332 : W := mkw 0xffeeedb123540000 0x63ffdddb6246a800 0xfffffff803fe003f 0x4ffffffff007fc00

def z333 : W := mkw 0x72c0000269140000 0x22e5800004d22800 0x7ee000047f9e005b 0x98fdc00008ff3c00

def z334 : W := mkw 0xfffffff7dee1fb78 0x57ffffffefbdc3f6 0xffffffffffe1ffff 0xffffffffffffc3ff

def z335 : W := mkw 0x2290362c108916d4 0x0845206c5821122d 0x6690fe3800011fbb 0x40cd21fc7000023f

def z336 : W := mkw 0x7a9df42efd19dce4 0x1af53be85dfa33b9 0xf89ff03ffc19fc6f 0xb7f13fe07ff833f8

def z337 : W := mkw 0x5010100658011040 0x02a020200cb00220 0xf810f007fc011c6f 0xb3f021e00ff80238

def z338 : W := mkw 0xfffeffbc108916d4 0x4bfffdff7821122d 0xfffffff800011fbf 0x47fffffff000023f

def z339 : W := mkw 0xa7c0000123540000 0x214f80000246a800 0x87e0000783fe0057 0xab0fc0000f07fc00

def z340 : W := mkw 0xa790362d33d916d4 0x094f206c5a67b22d 0xe790fe3ff3f91fff 0xfbcf21fc7fe7f23f

def z341 : W := mkw 0x850000036b540000 0x210a000006d6a800 0x87000007fffe0057 0xbb0e00000ffffc00

def z342 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x196881f80c67ffa4 0x6032d103f018cfff

def z343 : W := mkw 0x2abeffbc319916d4 0x48557dff7863322d 0x669ffffc73991ffb 0xdccd3ffff8e7323f

def z344 : W := mkw 0x2280000021100000 0x0045000000422000 0x7fe000047ffe005f 0xb8ffc00008fffc00

def z345 : W := mkw 0x082880d004226922 0x00105101a00844d2 0x000801c00000e000 0x00001003800001c0

def z346 : W := mkw 0xffddd007ff55d860 0x33ffbba00ffeabb0 0xfe1ff007ff81fc6f 0xb7fc3fe00fff03f8

def z347 : W := mkw 0x0000242000000000 0x0000004840000000 0x0010fe3800000020 0x400021fc70000000

def z348 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x000881f80c7fffe0 0x78001103f018ffff

def z349 : W := mkw 0xf7c66d236b540000 0x63ef8cda46d6a800 0xe6177e07f3800002 0x87cc2efc0fe70000

def z350 : W := mkw 0xffeeedb800080480 0x43ffdddb70001009 0xfffffff800191fff 0x5ffffffff000323f

def z351 : W := mkw 0xffeeedb004004820 0x43ffdddb60080090 0xfffffff80c01fc7f 0x77fffffff01803f8

def z352 : W := mkw 0x8d2a8bd906ea6fba 0x051a5517b20dd4df 0x1fe88ff80ffffffd 0x783fd11ff01fffff

def z353 : W := mkw 0x0002090000000000 0x0000041200000000 0x001f0fc000000020 0x44003e1f80000000

def z354 : W := mkw 0x7a8cf42a7d185ca4 0x1af519e854fa30b9 0x7880f0387c181c08 0x10f101e070f83038

def z355 : W := mkw 0xffffeff7ebf5a358 0x67ffffdfefd7eb46 0xffffffffffffe3ff 0xffffffffffffffc7

def z356 : W := mkw 0xdd6ec9934a440000 0x63badd9326948800 0x996f01c38c660004 0x2732de038718cc00

def z357 : W := mkw 0xf7c66d2000000000 0x43ef8cda40000000 0xe71f7fc000000037 0x47ce3eff80000000

def z358 : W := mkw 0x7aece4b269140000 0x62f5d9c964d22800 0x78e0f0387c1e0008 0x10f1c1e070f83c00

def z359 : W := mkw 0x5000000248000000 0x02a0000004900000 0xe0000007f0000002 0x83c000000fe00000

def z360 : W := mkw 0x8540000102440000 0x210a800002048800 0x0160000000660000 0x0002c0000000cc00

def z361 : W := mkw 0xdd5dd007de45d860 0x33babba00fbc8bb0 0xf97ff007fc67fc6f 0xb7f2ffe00ff8cff8

def z362 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x18e881f80c1fffa8 0x5031d103f0183fff

def z363 : W := mkw 0x580dc002cc00c820 0x12b01b8005980190 0xf81ff0038c00e02f 0x27f03fe0071801c0

def z364 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf9fff007fc7ffc7f 0xbff3ffe00ff8fff8

def z365 : W := mkw 0xffeec9936b540000 0x63ffdd9326d6a800 0xffef01c7fffe005f 0xbfffde038ffffc00

def z366 : W := mkw 0x7addd006fd15d860 0x32f5bba00dfa2bb0 0xf8fff007fc1ffc6f 0xb7f1ffe00ff83ff8

def z367 : W := mkw 0x082eedf8042a6da2 0x40105ddbf00854db 0x19fffff80c7ffffd 0x7c33fffff018ffff

def z368 : W := mkw 0x580cc00004004820 0x02b0198000080090 0xf81ff0000c01fc6f 0x37f03fe0001803f8

def z369 : W := mkw 0x2290100431111040 0x0045202008622220 0x6690f00473991c7b 0x98cd21e008e73238

def z370 : W := mkw 0x582cc09000000000 0x02b0598120000000 0xf9fff1f80000003f 0x47f3ffe3f0000000

def z371 : W := mkw 0xf7d002076bd50250 0x23efa0040ed7aa04 0xfff00e07ffff03ff 0xfbffe01c0ffffe07

def z372 : W := mkw 0xf7c0000021100000 0x03ef800000422000 0xffe000047398005f 0x9bffc00008e73000

def z373 : W := mkw 0xf7d10007eb558040 0x23efa2000fd6ab00 0xffff0007ffffe07f 0xbffffe000fffffc0

def z374 : W := mkw 0xf7d77d26d8019040 0x53efaefa4db00320 0xe6177e07f0000002 0x87cc2efc0fe00000

def z375 : W := mkw 0xffeeedfb6f7e6da2 0x63ffdddbf6defcdb 0xffffffffffffffff 0xffffffffffffffff

def z376 : W := mkw 0xffe880936b540000 0x23ffd10126d6a800 0xffe881fffffe007f 0xfbffd103fffffc00

def z377 : W := mkw 0xf7d67f2c319916d4 0x4befacfe5863322d 0xe697fe3c73991ffb 0xdfcd2ffc78e7323f

def z378 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x010881f80061fff5 0x68021103f000c3ff

def z379 : W := mkw 0x580cd0025c005820 0x12b019a004b800b0 0xf81ff0007c001c2f 0x17f03fe000f80038

def z380 : W := mkw 0x8502090102400000 0x010a041202048000 0x871f0fc783e00077 0xef0e3e1f8f07c000

def z381 : W := mkw 0x2280000821180480 0x0045000010423009 0x6680803c73991ffb 0xd8cd010078e7323f

def z382 : W := mkw 0x2280242800080480 0x0045004850001009 0x6690fe3800191ffb 0x58cd21fc7000323f

def z383 : W := mkw 0xfffffdb7ff55d860 0x73fffffb6ffeabb0 0xfffffffffffffc7f 0xfffffffffffffff8

def z384 : W := mkw 0xd54000034a440000 0x23aa800006948800 0xf9600007fc66004f 0xb3f2c0000ff8cc00

def z385 : W := mkw 0x001110049401d860 0x10002220092803b0 0x000000000001fc00 0x00000000000003f8

def z386 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x86170e0783e1e3c2 0xaf0c2e1c0f07c3c7

def z387 : W := mkw 0x7accd0027d145820 0x32f599a004fa28b0 0x78e0f0007c1e1c08 0x10f1c1e000f83c38

def z388 : W := mkw 0x72c0000000000000 0x02e5800000000000 0x78e0000000000008 0x00f1c00000000000

def z389 : W := mkw 0x0010120431911254 0x0800202408632224 0x0000000473800000 0x8000000008e70000

def z390 : W := mkw 0x00133f6c90a9b7dc 0x0c00267ed921536f 0x001ffff80001ffa0 0x44003ffff00003ff

def z391 : W := mkw 0x8500000102400000 0x010a000002048000 0x8100000380600004 0x230200000700c000

def z392 : W := mkw 0x7a9cf62c319916d4 0x0af539ec5863322d 0xfe9ffe3c73991fff 0xdffd3ffc78e7323f

def z393 : W := mkw 0xd54000034a440000 0x23aa800006948800 0x9f6000078fe60057 0xab3ec0000f1fcc00

def z394 : W := mkw 0x00010002cc00c820 0x1000020005980190 0x000000038c00e000 0x20000000071801c0

def z395 : W := mkw 0x0010120410811250 0x0000202408210224 0x6610fe0473811ffb 0xd8cc21fc08e7023f

def z396 : W := mkw 0xffeeedb102400000 0x43ffdddb62048000 0xffffffff83e0007f 0xefffffffff07c000

def z397 : W := mkw 0xa7c20b4123f42318 0x254f84168247e846 0x07e00fc003fe0390 0x480fc01f8007fc07

def z398 : W := mkw 0x083b8bdc84abeffa 0x04107717b90957df 0x001f8ff80001ffa0 0x44003f1ff00003ff

def z399 : W := mkw 0x85130b4d86ebeffa 0x050a26169b0dd7df 0x871f0fc78ffffff7 0xff0e3e1f8f1fffff

def z400 : W := mkw 0x082880d004226922 0x00105101a00844d2 0x196881c00c67fc6d 0x3032d1038018cff8

def z401 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x008881f80019fff9 0x58011103f00033ff

def z402 : W := mkw 0x85130b0582c18258 0x050a26160b058304 0x86170e07838103f3 0xcf0c2e1c0f070207

def z403 : W := mkw 0x85130b0582c18258 0x050a26160b058304 0x861f0e078381e067 0xa70c3e1c0f0703c0

def z404 : W := mkw 0xa7923f2c319916d4 0x094f247e5863322d 0xe79ffffc73991fff 0xdfcf3ffff8e7323f

def z405 : W := mkw 0x85130b4d82e9a7d8 0x050a26169b05d34f 0x879f8fff83f9ffff 0xff0f3f1fff07f3ff

def z406 : W := mkw 0x0000020821980694 0x080000041043300d 0x0000000003980380 0x0800000000073007

def z407 : W := mkw 0x22933f6cb1b9b7dc 0x0c45267ed963736f 0x669ffffc7399fffb 0xdccd3ffff8e733ff

def z408 : W := mkw 0xfffefffc35bb7ff6 0x4bfffdfff86b76ff 0xfffffffc7fffffff 0xfffffffff8ffffff

def z409 : W := mkw 0x0015500490019040 0x10002aa009200320 0x0017700000000000 0x04002ee000000000

def z410 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0x981ff0038c01fc24 0x27303fe0071803f8

def z411 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0x7800f007fc01fc48 0xb0f001e00ff803f8

def z412 : W := mkw 0x72c000036b540000 0x22e5800006d6a800 0x78e00007fffe0048 0xb8f1c0000ffffc00

def z413 : W := mkw 0x7aece4f8042a6da2 0x42f5d9c9f00854db 0x79e8f1f80c7ffffd 0x78f3d1e3f018ffff

def z414 : W := mkw 0x50155006d8019040 0x12a02aa00db00320 0xe01f7007f001e067 0xa7c03ee00fe003c0

def z415 : W := mkw 0xa780000123500000 0x014f00000246a000 0xe7800007f3f8005f 0xbbcf00000fe7f000

def z416 : W := mkw 0x0010120f7bdd16d4 0x280020241ef7ba2d 0x00000007ffff1fc0 0xb80000000ffffe3f

def z417 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x180881f80c01ffed 0x70301103f01803ff

def z418 : W := mkw 0x0828809004004820 0x0010510120080090 0x19e881f80c01fc7d 0x7033d103f01803f8

def z419 : W := mkw 0x7afdf4b6dc01d860 0x52f5fbe96db803b0 0xf8fff03ffc01fc6f 0xb7f1ffe07ff803f8

def z420 : W := mkw 0x0011024480a1a358 0x0400220489014346 0x000000000001e380 0x00000000000003c7

def z421 : W := mkw 0x0010020400810250 0x0000200408010204 0x06100e0403800002 0x800c201c08070000

def z422 : W := mkw 0xffe8809b6f5e4ca2 0x23ffd10136debc99 0xffe0803ffffe1c5f 0xbbffc1007ffffc38

def z423 : W := mkw 0x000100418260a108 0x040002008304c142 0x000000038060e000 0x200000000700c1c0

def z424 : W := mkw 0xf7d11007ff55d860 0x33efa2200ffeabb0 0xffe00007fffffc5f 0xbbffc0000ffffff8

def z425 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x0690fe3803991fb0 0x480d21fc7007323f

def z426 : W := mkw 0x85020b0102c00218 0x050a041602058004 0x06000e0003800000 0x000c001c00070000

def z427 : W := mkw 0x85130b4480a1a358 0x050a261689014346 0x871f0fc00001e3b7 0x470e3e1f800003c7

def z428 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e881f80c7efc0c 0x3033d103f018fdf8

def z429 : W := mkw 0x581fdb46dca1fb78 0x16b03fb68db943f6 0xf81fffc7fc01ffef 0xf7f03fff8ff803ff

def z430 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x87170fc783e00392 0xcf0e2e1f8f07c007

def z431 : W := mkw 0x2aa8a4b000000000 0x0055514960000000 0x7ff8fff80000003f 0x40fff1fff0000000

def z432 : W := mkw 0x0010124c35bb7ff6 0x08002024986b76ff 0x000000047fffffc0 0xb800000008ffffff

def z433 : W := mkw 0x2290362431911254 0x0845206c48632224 0x6610fe0473811c6b 0x90cc21fc08e70238

def z434 : W := mkw 0x7afcf6bc319916d4 0x4af5f9ed7863322d 0x7ef0fe3c73991ffb 0xd8fde1fc78e7323f

def z435 : W := mkw 0x0828809000000000 0x0010510120000000 0x196801c000000004 0x0032d00380000000

def z436 : W := mkw 0x0808800004004820 0x0010110000080090 0x000880000001fc20 0x00001100000003f8

def z437 : W := mkw 0xfffffdfedc2bfde2 0x53fffffbfdb857fb 0xfffffffffc7fffff 0xfffffffffff8ffff

def z438 : W := mkw 0xafeaadb000000000 0x415fd55b60000000 0x1fe88ff80000003d 0x403fd11ff0000000

def z439 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0x7fe000007ffe0018 0x18ffc00000fffc00

def z440 : W := mkw 0x00111007ff55d860 0x300022200ffeabb0 0x00000007fffffc40 0xb80000000ffffff8

def z441 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x18e080380c7fffc8 0x3831c1007018ffff

def z442 : W := mkw 0xf7c209036b540000 0x23ef841206d6a800 0xffff0fc7fffe007f 0xfffffe1f8ffffc00

def z443 : W := mkw 0x2ab8b6bc359b5ef6 0x0855716d786b36bd 0x7ef0fe3c7f9f1ffb 0xd8fde1fc78ff3e3f

def z444 : W := mkw 0x2290362f7bdd16d4 0x2845206c5ef7ba2d 0x6690fe3fffff1ffb 0xf8cd21fc7ffffe3f

def z445 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe00007f380001f 0x83ffc0000fe70000

def z446 : W := mkw 0x0010120c319916d4 0x080020241863322d 0x0080803c73991ff9 0xd801010078e7323f

def z447 : W := mkw 0x8502090000000000 0x010a041200000000 0x810f01c000000004 0x07021e0380000000

def z448 : W := mkw 0x0000000102400000 0x0000000002048000 0x0000000783e00040 0xa80000000f07c000

def z449 : W := mkw 0xffe880d36f766922 0x23ffd101a6deecd2 0xffe801c7fffee05f 0xbbffd0038ffffdc0

def z450 : W := mkw 0x0010362c108916d4 0x0800206c5821122d 0x0610fe3c03811ff3 0xc80c21fc7807023f

def z451 : W := mkw 0x580dc002cc00c820 0x12b01b8005980190 0x980f80038c01fc6d 0x37301f00071803f8

def z452 : W := mkw 0x22b036fc31bb37d6 0x0845606df863766f 0x67f0fffc73ff1ffb 0xd8cfe1fff8e7fe3f

def z453 : W := mkw 0x85130b0582c18258 0x050a26160b058304 0x871f0fc783800037 0xc70e3e1f8f070000

def z454 : W := mkw 0x5000000000000000 0x02a0000000000000 0xf80000000000000f 0x03f0000000000000

def z455 : W := mkw 0xdd1dd007de41d860 0x13ba3ba00fbc83b0 0xff1ff007ffe1fc7f 0xbffe3fe00fffc3f8

def z456 : W := mkw 0x2280000021100000 0x0045000000422000 0x6600000473800002 0x80cc000008e70000

def z457 : W := mkw 0x2280242000000000 0x0045004840000000 0x66107e0000000002 0x00cc20fc00000000

def z458 : W := mkw 0x228000036b540000 0x2045000006d6a800 0x66800007fffe005b 0xb8cd00000ffffc00

def z459 : W := mkw 0x00000048042a6da2 0x00000000900854db 0x000000000001ff80 0x00000000000003ff

def z460 : W := mkw 0xd54000034a440000 0x23aa800006948800 0x99e000038c7e005d 0x3b33c0000718fc00

def z461 : W := mkw 0x00111006d8019040 0x100022200db00320 0x00000007f0000000 0x800000000fe00000

def z462 : W := mkw 0x083882dc04ab6ff2 0x00107105b80956df 0x1ff88ffc0fffffff 0xf83ff11ff81fffff

def z463 : W := mkw 0xffffeff480a1a358 0x47ffffdfe9014346 0xfffffff80001e3bf 0x47fffffff00003c7

def z464 : W := mkw 0x000010025c005820 0x1000002004b800b0 0x000000007c001c00 0x1000000000f80038

def z465 : W := mkw 0xffece4b000000000 0x43ffd9c960000000 0xffe0f0380000001f 0x03ffc1e070000000

def z466 : W := mkw 0x08288098040a4ca2 0x0010510130081499 0x19e881f80c1e1c3d 0x5033d103f0183c38

def z467 : W := mkw 0xdd7fcbd582e1a358 0x47baff97ab05c346 0x9f7f0fc783e1e3f7 0xef3efe1f8f07c3c7

def z468 : W := mkw 0x580cc00000000000 0x02b0198000000000 0x980f000000000004 0x07301e0000000000

def z469 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80c7e007f 0x7ffffffff018fc00

def z470 : W := mkw 0x2aa8a6f825ba6fb6 0x0855514df04b74df 0x1fe88ff80ffffffd 0x783fd11ff01fffff

def z471 : W := mkw 0x08288098040a4ca2 0x0010510130081499 0x18e080380c1f1ff9 0x5831c10070183e3f

def z472 : W := mkw 0x00130b0480818258 0x0400261609010304 0x00170e0000000000 0x04002e1c00000000

def z473 : W := mkw 0x002000d8042a6da2 0x00004001b00854db 0x01e001f80c7fffd0 0x7803c003f018ffff

def z474 : W := mkw 0x082880d004226922 0x00105101a00844d2 0x196801c00c67e3f5 0x6832d0038018cfc7

def z475 : W := mkw 0x083effbc108916d4 0x48107dff7821122d 0x001ffff800011fa0 0x44003ffff000023f

def z476 : W := mkw 0xafeaadf8042a6da2 0x415fd55bf00854db 0x1fe88ff80c7ffffd 0x783fd11ff018ffff

def z477 : W := mkw 0x2280000021100000 0x0045000000422000 0x6080000070180008 0x10c1000000e03000

def z478 : W := mkw 0xd50000034a400000 0x03aa000006948000 0xff000007ffe0005f 0xbbfe00000fffc000

def z479 : W := mkw 0x0010024400a12350 0x0000200488014246 0x07180fc403e1e3f7 0xe80e301f8807c3c7

def z480 : W := mkw 0xf7c000436b742100 0x23ef800086d6e842 0xffe801c7ffffe3ff 0xfbffd0038fffffc7

def z481 : W := mkw 0x8500000102400000 0x010a000002048000 0x9fe000078ffe005f 0xbb3fc0000f1ffc00

def z482 : W := mkw 0x2280342831181484 0x0845006850623029 0x6680f03c73981c5b 0x98cd01e078e73038

def z483 : W := mkw 0xffeeefb821980694 0x4bffdddf7043300d 0xfffffff8039803bf 0x4ffffffff0073007

def z484 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x66907e3c73980392 0xc8cd20fc78e73007

def z485 : W := mkw 0xa7c0000123540000 0x214f80000246a800 0x0600000003800000 0x000c000000070000

def z486 : W := mkw 0x0818900414015860 0x00103120082802b0 0x7818f0047c01fc6f 0xb0f031e008f803f8

def z487 : W := mkw 0x7a9df426dc01d860 0x12f53be84db803b0 0xfe9ffe3ffc01fc7f 0xf7fd3ffc7ff803f8

def z488 : W := mkw 0x8511024582e1a358 0x050a22048b05c346 0x8700000783e1e3d7 0xab0e00000f07c3c7

def z489 : W := mkw 0xdd4dc003ce44c820 0x33ba9b80079c8990 0x996f00038c66e004 0x2732de000718cdc0

def z490 : W := mkw 0x083982dd86ebeffa 0x04107305bb0dd7df 0x19e881ff8ffffffd 0xf833d103ff1fffff

def z491 : W := mkw 0xf7c66d2000000000 0x43ef8cda40000000 0xe697fe380000003b 0x47cd2ffc70000000

def z492 : W := mkw 0x7a8ce42000000000 0x02f519c840000000 0xfe9ffe380000003f 0x47fd3ffc70000000

def z493 : W := mkw 0x2280000000000000 0x0045000000000000 0x668000000000001b 0x00cd000000000000

def z494 : W := mkw 0x0010362c319916d4 0x0800206c5863322d 0x0010fe3c73991fe0 0xd80021fc78e7323f

def z495 : W := mkw 0x081980048401c860 0x0010330009080390 0x981f80078c01fc6f 0xb7303f000f1803f8

def z496 : W := mkw 0xdd6fc9d18260a108 0x47badf93a304c142 0x996f01c38060e004 0x2732de038700c1c0

def z497 : W := mkw 0x0011104edc2bfde2 0x100022209db857fb 0x00000007fc7fffc0 0xb80000000ff8ffff

def z498 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e801f80c7ee394 0x6833d003f018fdc7

def z499 : W := mkw 0x72c0000269140000 0x22e5800004d22800 0xf8e00007fc1e004f 0xb3f1c0000ff83c00

def z500 : W := mkw 0x0808800804084ca0 0x0010110010081099 0x188880380c19fffd 0x78311100701833ff

def z501 : W := mkw 0x0000100831181484 0x0800002010623029 0x0000000070181c00 0x1000000000e03038

def z502 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e081f80c7e1f98 0x5833c103f018fc3f

def z503 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6080f03c73991fc8 0x98c101e078e7323f

def z504 : W := mkw 0x00111006dc01d860 0x100022200db803b0 0x801f0007fc01fc67 0xb7003e000ff803f8

def z505 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xfe000007ff80004f 0xb3fc00000fff0000

def z506 : W := mkw 0x85020b4102e02318 0x050a04168205c046 0x07080fc003e1e3f5 0x680e101f8007c3c7

def z507 : W := mkw 0xa7933f2db3d996dc 0x0d4f267e5b67b32d 0xe697fe3ff3991ffb 0xdfcd2ffc7fe7323f

def z508 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x811f0fc38061e3a4 0x67023e1f8700c3c7

def z509 : W := mkw 0x0000000269140000 0x2000000004d22800 0x000000007c1e0000 0x1000000000f83c00

def z510 : W := mkw 0xffe880d8042a6da2 0x03ffd101b00854db 0xffe881f80c7fffff 0x7bffd103f018ffff

def z511 : W := mkw 0x0010100410011040 0x0000202008200220 0x0010f00000011c20 0x000021e000000238

def z512 : W := mkw 0xf7d036277bd51254 0x2befa06c4ef7aa24 0xe6107e07f3800002 0x83cc20fc0fe70000

def z513 : W := mkw 0x0808804004206920 0x00101100800840d2 0x190881c00c61fffd 0x783211038018c3ff

def z514 : W := mkw 0xffccc0036b540000 0x23ff998006d6a800 0xfffff007fffe007f 0xbfffffe00ffffc00

def z515 : W := mkw 0x8562099000000000 0x410ac41320000000 0x016001c000000000 0x0002c00380000000

def z516 : W := mkw 0xdd7fd996dc01d860 0x53baffb32db803b0 0xf97ff1c7fc01fc6f 0xb7f2ffe38ff803f8

def z517 : W := mkw 0x00111247dee1fb78 0x140022248fbdc3f6 0x00000007ffe1ffc0 0xb80000000fffc3ff

def z518 : W := mkw 0x0000020000800210 0x0000000400010004 0x06000e0003800390 0x480c001c00070007

def z519 : W := mkw 0x00130b4480a1a358 0x0400261689014346 0x011f0fc00061e3f5 0x6c023e1f8000c3c7

def z520 : W := mkw 0x2290342c311914c4 0x0845206858623229 0x6090f03c70191c6b 0x90c121e078e03238

def z521 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x06800e3c73991fd0 0xd80d001c78e7323f

def z522 : W := mkw 0x5004400000000000 0x02a0088000000000 0xe017700000000002 0x07c02ee000000000

def z523 : W := mkw 0x2280262821980694 0x0845004c5043300d 0x6690fe38039803bb 0x48cd21fc70073007

def z524 : W := mkw 0x2290020421910250 0x0045200408432204 0x66900e04739903fb 0xd8cd201c08e73207

def z525 : W := mkw 0x8d3feff582e1a358 0x451a7fdfeb05c346 0x871fffff83e1e3f7 0xef0e3fffff07c3c7

def z526 : W := mkw 0xa7c0000123540000 0x214f80000246a800 0x1fe000000ffe005d 0x383fc000001ffc00

def z527 : W := mkw 0x083990dedc2bfde2 0x10107321bdb857fb 0x19e881fffc7ffffd 0xf833d103fff8ffff

def z528 : W := mkw 0xa7f32ff582e1a358 0x454fe65feb05c346 0x87ff0fff83e1e3f7 0xef0ffe1fff07c3c7

def z529 : W := mkw 0xf7c2090000000000 0x03ef841200000000 0xffff0fc00000003f 0x47fffe1f80000000

def z530 : W := mkw 0xffeeedf000202100 0x43ffdddbe0004042 0xfffffff80061e3ff 0x6ffffffff000c3c7

def z531 : W := mkw 0x7aece4b000000000 0x42f5d9c960000000 0x7ef0fe380000003b 0x40fde1fc70000000

def z532 : W := mkw 0x08288098040a4ca2 0x0010510130081499 0x19e080380c7e1c5d 0x3833c1007018fc38

def z533 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81f7007fc00e006 0xa7f03ee00ff801c0

def z534 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfef7fe380000000a 0x07fdeffc70000000

def z535 : W := mkw 0x0010362c108916d4 0x0800206c5821122d 0x6010fe3c70011feb 0xd0c021fc78e0023f

def z536 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0x781ff0007c01fc28 0x14f03fe000f803f8

def z537 : W := mkw 0x583dd09edc0bdce2 0x12b07ba13db817b9 0xf8fff03ffc1ffc6f 0xb7f1ffe07ff83ff8

def z538 : W := mkw 0x083980dc842bede2 0x00107301b90857db 0x99ff81ff8c7fffff 0xff33ff03ff18ffff

def z539 : W := mkw 0xf7c20b436bf42318 0x27ef841686d7e846 0xffe00fc7fffe03df 0xfbffc01f8ffffc07

def z540 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xe6800007f398005b 0x9bcd00000fe73000

def z541 : W := mkw 0x0010020400810250 0x0000200408010204 0x00000004038103c0 0x8800000008070207

def z542 : W := mkw 0xf7c30943eb74a108 0x27ef861287d6e942 0xffef01c7fffee05f 0xbfffde038ffffdc0

def z543 : W := mkw 0xf7c000034a440000 0x23ef800006948800 0xffe000038c66001f 0x23ffc0000718cc00

def z544 : W := mkw 0xf7d036277bd51254 0x2befa06c4ef7aa24 0xfff07e07fffe005f 0xbbffe0fc0ffffc00

def z545 : W := mkw 0xdd6880d34e666922 0x23bad101a69cccd2 0x996801c38c66e004 0x2332d0038718cdc0

def z546 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0x9fef0ff800000014 0x473fde1ff0000000

def z547 : W := mkw 0x22e024b000000000 0x4045c04960000000 0x00e0003800000000 0x0001c00070000000

def z548 : W := mkw 0x0010362c108916d4 0x0800206c5821122d 0x0090fe3800191ff9 0x580121fc7000323f

def z549 : W := mkw 0xdd6ec9d004226922 0x43badd93a00844d2 0x996f01c00c66e004 0x2732de038018cdc0

def z550 : W := mkw 0x080cd00014005820 0x101019a0002800b0 0x0000f00000001c00 0x000001e000000038

def z551 : W := mkw 0x2290342410011040 0x0045206848200220 0x6690fe3c70011c7b 0xd0cd21fc78e00238

def z552 : W := mkw 0x8d3b8bd586e3eb7a 0x051a7717ab0dc7d6 0x9f7f0fc78fe7e3f7 0xef3efe1f8f1fcfc7

def z553 : W := mkw 0x0010100c100914c0 0x0000202018201229 0x6090f03c70191ffb 0xd8c121e078e0323f

def z554 : W := mkw 0xa7c22d2000000000 0x414f845a40000000 0x06000e0000000000 0x000c001c00000000

def z555 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf817f007fc001c0a 0x97f02fe00ff80038

def z556 : W := mkw 0x0828809000000000 0x0010510120000000 0x18e0803800000008 0x0031c10070000000

def z557 : W := mkw 0xffddf62fffdddef4 0x3bffbbec5fffbbbd 0xfffffe3fffffffff 0xfffffffc7fffffff

def z558 : W := mkw 0x586cc09000000000 0x42b0d98120000000 0x1860000000000000 0x0030c00000000000

def z559 : W := mkw 0x08288098040a4ca2 0x0010510130081499 0x18e880380c1ffc6d 0x3031d10070183ff8

def z560 : W := mkw 0x581dd247dee1fb78 0x16b03ba48fbdc3f6 0xf81ff007ffe1ffef 0xbff03fe00fffc3ff

def z561 : W := mkw 0x8d3b8bd582e1a358 0x051a7717ab05c346 0x9fff8fff83e1e3ff 0xef3fff1fff07c3c7

def z562 : W := mkw 0x582cd09a5c0a5ca2 0x12b059a134b814b9 0x78e0f0387c1e1c08 0x10f1c1e070f83c38

def z563 : W := mkw 0x581cd0065c015860 0x12b039a00cb802b0 0x7810f0047c011c6b 0x90f021e008f80238

def z564 : W := mkw 0x082880d004226922 0x00105101a00844d2 0x19e801c00c7ee05d 0x3833d0038018fdc0

def z565 : W := mkw 0x083dd0dc942bfde2 0x10107ba1b92857fb 0x19fff1f80c7ffffd 0x7c33ffe3f018ffff

def z566 : W := mkw 0xfffefdb410011040 0x43fffdfb68200220 0xfffffffc70011c7f 0xd7fffffff8e00238

def z567 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xf9e00003fc7e000c 0x33f3c00007f8fc00

def z568 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xff7f7fc000000006 0x07fefeff80000000

def z569 : W := mkw 0xa7e22db000000000 0x414fc45b60000000 0x67f0fff80000003b 0x40cfe1fff0000000

def z570 : W := mkw 0x85133f6d92e9b7dc 0x0d0a267edb25d36f 0x871fffff83e1fff7 0xef0e3fffff07c3ff

def z571 : W := mkw 0xa7932f6582e1a358 0x054f265ecb05c346 0xe79fffff83e1e3ff 0xefcf3fffff07c3c7

def z572 : W := mkw 0x7abdf6fefdbbfff6 0x1af57bedfdfb77ff 0xffffffffffffffff 0xffffffffffffffff

def z573 : W := mkw 0x0011020480818250 0x0000220409010304 0x861f0e078381e3f7 0xef0c3e1c0f0703c7

def z574 : W := mkw 0x00110247ebf5a358 0x240022048fd7eb46 0x00000007ffffe3c0 0xb80000000fffffc7

def z575 : W := mkw 0x2280262821980694 0x0845004c5043300d 0x06808e3803991ff9 0x580d011c7007323f

def z576 : W := mkw 0x580dc002cc00c820 0x12b01b8005980190 0xf80f0007fc00e04f 0xb7f01e000ff801c0

def z577 : W := mkw 0x8d1fdb4596e1fb78 0x151a3fb68b2dc3f6 0x871fffc783e1fff7 0xef0e3fff8f07c3ff

def z578 : W := mkw 0x72d0362e799d16d4 0x2ae5a06c5cf33a2d 0x7ef0fe3c7f9f1ffb 0xd8fde1fc78ff3e3f

def z579 : W := mkw 0x0828809004024822 0x0010510120080490 0x186000000c060000 0x0030c00000180c00

def z580 : W := mkw 0x2aa8a4f8042a6da2 0x00555149f00854db 0x7ff8fff80c7fffff 0x78fff1fff018ffff

def z581 : W := mkw 0x0011100490019040 0x0000222009200320 0xe01ff007f001fc6f 0xb7c03fe00fe003f8

def z582 : W := mkw 0x0000000004004820 0x0000000000080090 0x000000000c01fc40 0x30000000001803f8

def z583 : W := mkw 0xfffdd0dfff7ffde2 0x33fffba1bffefffb 0xfffff1ffffffffff 0xffffffe3ffffffff

def z584 : W := mkw 0xa7932f6da3f9a7dc 0x0d4f265edb47f34f 0x879f0fff83f9e3f7 0xef0f3e1fff07f3c7

def z585 : W := mkw 0x2280000021100000 0x0045000000422000 0x0680000003980010 0x080d000000073000

def z586 : W := mkw 0x000309408020a108 0x0400061281004142 0x000f01c00000e000 0x04001e03800001c0

def z587 : W := mkw 0x0828809000000000 0x0010510120000000 0x19e881f80c7e007d 0x7833d103f018fc00

def z588 : W := mkw 0xa7e000d9237e2582 0x214fc001b246fc4b 0x07e001f803fe0390 0x480fc003f007fc07

def z589 : W := mkw 0x082880d004226922 0x00105101a00844d2 0x19e881f80c66e03d 0x6033d103f018cdc0

def z590 : W := mkw 0xa7d0362d33dd16d4 0x294fa06c5a67ba2d 0x67f0fe3c73ff1ffb 0xd8cfe1fc78e7fe3f

def z591 : W := mkw 0x8d1b8b4586e1eb78 0x051a37168b0dc3d6 0x9f1f8fc78fe1ffff 0xff3e3f1f8f1fc3ff

def z592 : W := mkw 0x002000d8002a2582 0x00004001b000544b 0x000001f800000380 0x40000003f0000007

def z593 : W := mkw 0x0020009000000000 0x0000400120000000 0x01e001f800000010 0x4003c003f0000000

def z594 : W := mkw 0x8d2b89d18662e92a 0x051a5713a30cc5d2 0x996f01c38c66e004 0x2732de038718cdc0

def z595 : W := mkw 0x8500000102400000 0x010a000002048000 0x8600000783800002 0x830c00000f070000

def z596 : W := mkw 0x2291366db3f9b7dc 0x0c45226cdb67f36f 0x6690fe3ff3f9fffb 0xf8cd21fc7fe7f3ff

def z597 : W := mkw 0xdd6ec99000000000 0x43badd9320000000 0x99ef81f80000003d 0x4733df03f0000000

def z598 : W := mkw 0x2290366c35bb7ff6 0x0845206cd86b76ff 0x6690fe3c7ffffffb 0xf8cd21fc78ffffff

def z599 : W := mkw 0x0010020400810250 0x0000200408010204 0x00100e00000103a0 0x4000201c00000207

def z600 : W := mkw 0x72957626f9919254 0x1ae52aec4df32324 0xe6177e07f3800002 0x87cc2efc0fe70000

def z601 : W := mkw 0x581df62edc89def4 0x1ab03bec5db913bd 0xf81ffe3ffc01ffef 0xf7f03ffc7ff803ff

def z602 : W := mkw 0x081dd0049401d860 0x10103ba0092803b0 0x801ff0078001fc67 0xa7003fe00f0003f8

def z603 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc783e0e006 0xa70e3e1f8f07c1c0

def z604 : W := mkw 0xdd1fdb07dec1da78 0x17ba3fb60fbd83b4 0xfe1ffe07ff81fc6f 0xb7fc3ffc0fff03f8

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x6010f0000000002b 0x00c021e000000000

def z606 : W := mkw 0xdd1fd906dc01d860 0x13ba3fb20db803b0 0xff1fffc7fc01fc7f 0xf7fe3fff8ff803f8

def z607 : W := mkw 0xffffeffd86ebeffa 0x47ffffdffb0dd7df 0xffffffff8fffffff 0xffffffffff1fffff

def z608 : W := mkw 0x081dd006dc01d860 0x10103ba00db803b0 0x001ff007fc01fc60 0xb4003fe00ff803f8

def z609 : W := mkw 0x50054002c8008000 0x12a00a8005900100 0x8007000380000000 0x07000e0007000000

def z610 : W := mkw 0x7a9df626fd91da74 0x1af53bec4dfb23b4 0xfe1ffe07ff81fc6f 0xb7fc3ffc0fff03f8

def z611 : W := mkw 0x0000004b6f7e6da2 0x2000000096defcdb 0x00000007ffffffc0 0xb80000000fffffff

def z612 : W := mkw 0xffeeeff102e02318 0x47ffdddfe205c046 0xfffffff803e003bf 0x4ffffffff007c007

def z613 : W := mkw 0xf7c0000b6b5c0480 0x23ef800016d6b809 0xffe0803fffff1fff 0xfbffc1007ffffe3f

def z614 : W := mkw 0x0808800004004820 0x0010110000080090 0x180800000c00e004 0x20301000001801c0

def z615 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xe7000007f3e00057 0xabce00000fe7c000

def z616 : W := mkw 0x081df62c9489def4 0x18103bec592913bd 0x001ffe380001ffa0 0x44003ffc700003ff

def z617 : W := mkw 0x85131b4db3f9b7dc 0x0d0a26369b67f36f 0x871f0fc7f3f9fff7 0xff0e3e1f8fe7f3ff

def z618 : W := mkw 0xf7d55007fb559040 0x33efaaa00ff6ab20 0xe6177007f3800002 0x87cc2ee00fe70000

def z619 : W := mkw 0x0808800004004820 0x0010110000080090 0x180080000c001c08 0x1030010000180038

def z620 : W := mkw 0x082880d000202100 0x00105101a0004042 0x19e881f80061e3fd 0x6833d103f000c3c7

def z621 : W := mkw 0xff9fff6ffff9fffc 0x1fff3ffedffff3ff 0xff9ffffffff9ffff 0xffff3ffffffff3ff

def z622 : W := mkw 0x2aa8b4f8353a7da6 0x08555169f06a74fb 0x79e8f1f87c7ffffd 0x78f3d1e3f0f8ffff

def z623 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x810f01c783e1e3c4 0xaf021e038f07c3c7

def z624 : W := mkw 0x7290362e799916d4 0x0ae5206c5cf3322d 0xfe90fe3fff991fff 0xfbfd21fc7fff323f

def z625 : W := mkw 0x22a026f821ba2796 0x0845404df043744f 0x07e00ff803fe0390 0x480fc01ff007fc07

def z626 : W := mkw 0x00000008040a4ca2 0x0000000010081499 0x000000000c1e1c00 0x1000000000183c38

def z627 : W := mkw 0xdd6ec9d8042a6da2 0x43badd93b00854db 0x99ef81f80c7ffffd 0x7f33df03f018ffff

def z628 : W := mkw 0x002000d8002a2582 0x00004001b000544b 0x01e801f8007fe3f5 0x6803d003f000ffc7

def z629 : W := mkw 0x2290362431911254 0x0845206c48632224 0x66907e047398005b 0x98cd20fc08e73000

def z630 : W := mkw 0x002000d8002a2582 0x00004001b000544b 0x01e081f8007f1ff9 0x5803c103f000fe3f

def z631 : W := mkw 0xf7c0242000000000 0x03ef804840000000 0xfff0fe380000003f 0x43ffe1fc70000000

def z632 : W := mkw 0x500000036b540000 0x22a0000006d6a800 0xf8000007fffe004f 0xbbf000000ffffc00

def z633 : W := mkw 0xffece4b36b540000 0x63ffd9c966d6a800 0xffe0f03ffffe005f 0xbbffc1e07ffffc00

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000403800053 0x880c000008070000

def z635 : W := mkw 0x082eedf8042a6da2 0x40105ddbf00854db 0x001ffff80001ffa0 0x44003ffff00003ff

def z636 : W := mkw 0x2280262821980694 0x0845004c5043300d 0x66800e3c739803db 0xd8cd001c78e73007

def z637 : W := mkw 0x083890dc142b7de2 0x00107121b82856fb 0x79f8f1fc7c7fffff 0xf8f3f1e3f8f8ffff

def z638 : W := mkw 0x0010100410011040 0x0000202008200220 0x0000000470011c40 0x9000000008e00238

def z639 : W := mkw 0x2280262021900214 0x0845004c40432004 0x06000e0003800000 0x000c001c00070000

def z640 : W := mkw 0x85120b4502e12358 0x050a24168a05c246 0x07100fc403e103f3 0xc80e201f8807c207

def z641 : W := mkw 0x582cd0da5c2a7da2 0x12b059a1b4b854fb 0x79e8f1f87c7ffffd 0x78f3d1e3f0f8ffff

def z642 : W := mkw 0x582cc0d8042a6da2 0x02b05981b00854db 0xf9fff1f80c7fffff 0x7ff3ffe3f018ffff

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000780000047 0xa30000000f000000

def z644 : W := mkw 0xf7d55007fb559040 0x33efaaa00ff6ab20 0xfff77007fffe005f 0xbfffeee00ffffc00

def z645 : W := mkw 0x2ab8b6bc319916d4 0x0855716d7863322d 0x7ff8fffc73991fff 0xd8fff1fff8e7323f

def z646 : W := mkw 0xf7e22db000000000 0x43efc45b60000000 0xffe00ff80000001f 0x43ffc01ff0000000

def z647 : W := mkw 0xdd6fc992cc00c820 0x53badf9325980190 0x996f01c38c00e004 0x2732de03871801c0

def z648 : W := mkw 0x0000000248000000 0x0000000004900000 0x00000007fc000040 0xb00000000ff80000

def z649 : W := mkw 0x0808800004004820 0x0010110000080090 0x19e880000c7ffc7d 0x3833d1000018fff8

def z650 : W := mkw 0x08088048042a6da2 0x00101100900854db 0x180880000c7fffed 0x383011000018ffff

def z651 : W := mkw 0x581dd20efd99def4 0x1ab03ba41dfb33bd 0xf81ff007ff99ffef 0xbff03fe00fff33ff

def z652 : W := mkw 0x0000000800080480 0x0000000010001009 0x0000000000191fc0 0x180000000000323f

def z653 : W := mkw 0x0010362410811254 0x0800206c48210224 0x00107e0000000000 0x000020fc00000000

def z654 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3c73981c0a 0x90cd21fc78e73038

def z655 : W := mkw 0xffefedf18260a108 0x47ffdfdbe304c142 0xfffffffb8060e03f 0x67fffffff700c1c0

def z656 : W := mkw 0xf7d67f2431911254 0x4befacfe48632224 0xe6177e0473800002 0x87cc2efc08e70000

def z657 : W := mkw 0xdd1fcb4582e1a358 0x07ba3f968b05c346 0xff1fffc783e1e3ff 0xeffe3fff8f07c3c7

def z658 : W := mkw 0x082880d8002a2582 0x00105101b000544b 0x19e881f8007e03bd 0x4833d103f000fc07

def z659 : W := mkw 0x0010100410011040 0x0000202008200220 0x6010700470000002 0x80c020e008e00000

def z660 : W := mkw 0xa7c0000123540000 0x214f80000246a800 0x67e0000473fe005b 0x98cfc00008e7fc00

def z661 : W := mkw 0xf7d0120f7bdd16d4 0x2befa0241ef7ba2d 0xffe00007ffff1fdf 0xbbffc0000ffffe3f

def z662 : W := mkw 0xf7c0000269140000 0x23ef800004d22800 0xffe000007c1e001f 0x13ffc00000f83c00

def z663 : W := mkw 0xfff8b6ff7fff7ff6 0x2bfff16dfefffeff 0xfff8ffffffffffff 0xfbfff1ffffffffff

def z664 : W := mkw 0x0000262800880694 0x0800004c5001100d 0x00000e3800000380 0x4000001c70000007

def z665 : W := mkw 0x0000004800282580 0x000000009000504b 0x018881f80079fffd 0x78031103f000f3ff

def z666 : W := mkw 0x8d2b89d9866aedaa 0x051a5713b30cd5db 0x99ef81fb8c7ffffd 0x7f33df03f718ffff

def z667 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xff600007ffe60006 0xa3fec0000fffcc00

def z668 : W := mkw 0x083dd0dc942bfde2 0x10107ba1b92857fb 0x001ff1f80001ffa0 0x44003fe3f00003ff

def z669 : W := mkw 0x8500004102602100 0x010a00008204c042 0x870801c783e1e3f7 0xeb0e10038f07c3c7

def z670 : W := mkw 0xffe8809000000000 0x03ffd10120000000 0xffe881f80000003f 0x43ffd103f0000000

def z671 : W := mkw 0x5000000248000000 0x02a0000004900000 0x980000038c000004 0x2330000007180000

def z672 : W := mkw 0xf7c0000123540000 0x23ef80000246a800 0xffe0000003fe001f 0x0bffc0000007fc00

def z673 : W := mkw 0x081dd0049401d860 0x10103ba0092803b0 0x601ff0047001fc6b 0x94c03fe008e003f8

def z674 : W := mkw 0xf7d0362c319916d4 0x0befa06c5863322d 0xfff0fe3c73991fff 0xdbffe1fc78e7323f

def z675 : W := mkw 0x0000000800080480 0x0000000010001009 0x0000803800011fa0 0x400001007000023f

def z676 : W := mkw 0xffefedb2cc00c820 0x53ffdfdb65980190 0xfffffffb8c00e03f 0x67fffffff71801c0

def z677 : W := mkw 0xf7d10247ebf5a358 0x27efa2048fd7eb46 0xffe00007ffffe3df 0xbbffc0000fffffc7

def z678 : W := mkw 0xf7c0004b6f7e6da2 0x23ef800096defcdb 0xffe00007ffffffdf 0xbbffc0000fffffff

def z679 : W := mkw 0x0000004000202100 0x0000000080004042 0x010001c000600390 0x480200038000c007

def z680 : W := mkw 0x8d2a899000000000 0x011a551320000000 0x9fff8ff80000003f 0x473fff1ff0000000

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x06100e0000000033 0x400c201c00000000

def z682 : W := mkw 0x0000000021100000 0x0000000000422000 0x0000000473980040 0x9800000008e73000

def z683 : W := mkw 0xa7c0000000000000 0x014f800000000000 0x07e0000000000010 0x000fc00000000000

def z684 : W := mkw 0x00000048042a6da2 0x00000000900854db 0x010801c00c7ffff5 0x780210038018ffff

def z685 : W := mkw 0x0011024d86ebeffa 0x040022049b0dd7df 0x000000078fffffc0 0xb80000000f1fffff

def z686 : W := mkw 0x8503090182408008 0x050a061203048100 0x8007000380000000 0x07000e0007000000

def z687 : W := mkw 0x582dc0d2cc22e922 0x12b05b81a59845d2 0x996f01c38c66e004 0x2732de038718cdc0

def z688 : W := mkw 0x5040000248040000 0x22a0800004900800 0x186000000c060000 0x0030c00000180c00

def z689 : W := mkw 0x7a9cf62e7d995ef4 0x1af539ec5cfb32bd 0x7e90fe3c7f991ffb 0xd8fd21fc78ff323f

def z690 : W := mkw 0x8d2880d9066a6da2 0x011a5101b20cd4db 0x9fe881ff8fffffff 0xfb3fd103ff1fffff

def z691 : W := mkw 0xfffeffb431911254 0x4bfffdff68632224 0xfffffffc7380003f 0xc7fffffff8e70000

def z692 : W := mkw 0x0000100010001000 0x0000002000200020 0x6000f00070001c08 0x10c001e000e00038

def z693 : W := mkw 0x581dd00edc09dce0 0x12b03ba01db813b9 0xf89ff03ffc19ffff 0xfff13fe07ff833ff

def z694 : W := mkw 0x583dd0d6dc23f962 0x12b07ba1adb847f2 0xf97ff1c7fc67fc6f 0xb7f2ffe38ff8cff8

def z695 : W := mkw 0xdd3fdbdfdeebfffa 0x17ba7fb7bfbdd7ff 0xffffffffffffffff 0xffffffffffffffff

def z696 : W := mkw 0x85220bd902ea279a 0x050a4417b205d44f 0x07e00ff803fe0390 0x480fc01ff007fc07

def z697 : W := mkw 0x2290362431911254 0x0845206c48632224 0x6690fe3c7380003b 0xc0cd21fc78e70000

def z698 : W := mkw 0xa7d30b45a3f5a358 0x254fa6168b47eb46 0x87ff0fc783ffe3f7 0xef0ffe1f8f07ffc7

def z699 : W := mkw 0x081dd0049401d860 0x10103ba0092803b0 0x181ff0000c01fc6d 0x34303fe0001803f8

def z700 : W := mkw 0xd540000000000000 0x03aa800000000000 0x9960000000000004 0x0332c00000000000

def z701 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xe7e00007f3fe0012 0x8bcfc0000fe7fc00

def z702 : W := mkw 0xffeeedb8040a4ca2 0x43ffdddb70081499 0xfffffff80c1e1c3f 0x57fffffff0183c38

def z703 : W := mkw 0x8513090480018040 0x010a261209000300 0x871f0fc78001e077 0xe70e3e1f8f0003c0

def z704 : W := mkw 0x0000004000202100 0x0000000080004042 0x000801c00001e3a0 0x40001003800003c7

def z705 : W := mkw 0x0010000400010040 0x0000200008000200 0x0010000400010063 0x8000200008000200

def z706 : W := mkw 0x0011120efd99def4 0x180022241dfb33bd 0x00000007ff99ffc0 0xb80000000fff33ff

def z707 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xf9fffff80000002c 0x47f3fffff0000000

def z708 : W := mkw 0x8502094102602100 0x010a04128204c042 0x871f0fc783e1e3f7 0xef0e3e1f8f07c3c7

def z709 : W := mkw 0x082eedb36b540000 0x60105ddb66d6a800 0x001ffffffffe0060 0xfc003ffffffffc00

def z710 : W := mkw 0x7a8de62aed98ceb4 0x1af51bcc55db319d 0x9e8f0e3b8f98e394 0x6f3d1e1c771f31c7

def z711 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffff0007fffe007f 0xbffffe000ffffc00

def z712 : W := mkw 0x0011124db7fbfffe 0x0c0022249b6ff7ff 0x00000007ffffffc0 0xb80000000fffffff

def z713 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x181ffff80000002d 0x44303ffff0000000

def z714 : W := mkw 0x503550ded82bb5c2 0x12a06aa1bdb0576b 0xe1f771fff07e0392 0xcfc3eee3ffe0fc07

def z715 : W := mkw 0xa7833d69b378b58c 0x0d4f067ad366f16b 0xe18ff1fbf078fc0c 0x37c31fe3f7e0f1f8

def z716 : W := mkw 0xf7c209036b540000 0x23ef841206d6a800 0xffe00fc7fffe005f 0xfbffc01f8ffffc00

def z717 : W := mkw 0x7aece4ba6d1e4ca2 0x62f5d9c974da3c99 0x78e0f0387c1e1c08 0x10f1c1e070f83c38

def z718 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0xe690fe3ff3991fff 0xfbcd21fc7fe7323f

def z719 : W := mkw 0x7aeeedb000000000 0x42f5dddb60000000 0x7efffff80000003b 0x44fdfffff0000000

def z720 : W := mkw 0x582eedb000000000 0x42b05ddb60000000 0x781ffff800000028 0x44f03ffff0000000

def z721 : W := mkw 0x2ab8b6f435b37b76 0x0855716de86b66f6 0x7f787fc47fe6e006 0xa0fef0ff88ffcdc0

def z722 : W := mkw 0x50155006dc01d860 0x12a02aa00db803b0 0xe01f7007fc01fc67 0xb7c03ee00ff803f8

def z723 : W := mkw 0x2aaeedb021100000 0x40555ddb60422000 0x669ffffc7398007b 0xdccd3ffff8e73000

def z724 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0x7fe00007fffe0058 0xb8ffc0000ffffc00

def z725 : W := mkw 0x7aaeedb000000000 0x42f55ddb60000000 0xfe9ffff80000003f 0x47fd3ffff0000000

def z726 : W := mkw 0xffeeedb021100000 0x43ffdddb60422000 0xfffffff80398003f 0x4ffffffff0073000

def z727 : W := mkw 0x0011124ffbfdb7dc 0x2c0022249ff7fb6f 0x00000007ffffffc0 0xb80000000fffffff

def z728 : W := mkw 0xf7c22d236b540000 0x23ef845a46d6a800 0xfffffffffffe007f 0xfffffffffffffc00

def z729 : W := mkw 0x8d2eedb000000000 0x411a5ddb60000000 0x071ffff800000030 0x440e3ffff0000000

def z730 : W := mkw 0x082cc0d8042a6da2 0x00105981b00854db 0x19fff1f80c7ffffd 0x7c33ffe3f018ffff

def z731 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc783e1e3c6 0xaf0e3e1f8f07c3c7

def z732 : W := mkw 0xf7c440036b540000 0x23ef888006d6a800 0xfff77007fffe005f 0xbfffeee00ffffc00

def z733 : W := mkw 0x000000036b540000 0x2000000006d6a800 0x18e00007fffe0048 0xb831c0000ffffc00

def z734 : W := mkw 0xafaaadb000000000 0x015f555b60000000 0xfffffff80000003f 0x47fffffff0000000

def z735 : W := mkw 0x580cc0024c004820 0x02b0198004980090 0xf81ff007fc01fc6f 0xb7f03fe00ff803f8

def z736 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf80ff007fc01fc4c 0xb7f01fe00ff803f8

def z737 : W := mkw 0x8d3b8b9d86cbcefa 0x051a77173b0d979d 0x9ef78e3f8f9e1c0a 0x973def1c7f1f3c38

def z738 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80000000e 0x07fffffff0000000

def z739 : W := mkw 0x583dd096dc01d860 0x12b07ba12db803b0 0xf8fff03ffc01fc6f 0xb7f1ffe07ff803f8

def z740 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x7ff0fe3c73991fff 0xd8ffe1fc78e7323f

def z741 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf8fff007fc1ffc6f 0xb7f1ffe00ff83ff8

def z742 : W := mkw 0xafddd005b755d860 0x315fbba00b6eabb0 0x07fff00003fffc30 0x0c0fffe00007fff8

def z743 : W := mkw 0x2aaeedb000000000 0x40555ddb60000000 0x7ffffff80000003f 0x44fffffff0000000

def z744 : W := mkw 0x0010362c108916d4 0x0800206c5821122d 0x6610fe3c73811ffb 0xd8cc21fc78e7023f

def z745 : W := mkw 0xa7e22df9237e2582 0x614fc45bf246fc4b 0x07e00ff803fe0390 0x480fc01ff007fc07

def z746 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6610fe3c73811feb 0xd0cc21fc78e7023f

def z747 : W := mkw 0xd550362f5acd16d4 0x2baaa06c5eb59a2d 0x9970fe3b8c671fa4 0x6332e1fc7718ce3f

def z748 : W := mkw 0xdd7edb9c319916d4 0x4bbafdb73863322d 0x996f01c473991fc4 0x9f32de0388e7323f

def z749 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe00007fffe001a 0x9bffc0000ffffc00

def z750 : W := mkw 0xffeeedb004024822 0x43ffdddb60080490 0xfffffff80c06003f 0x47fffffff0180c00

def z751 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80c1e003f 0x57fffffff0183c00

def z752 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x79e881fc7c7fffff 0xf8f3d103f8f8ffff

def z753 : W := mkw 0x0000004800282580 0x000000009000504b 0x19e881f80c7ffffd 0x7833d103f018ffff

def z754 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xe61ffffff3800022 0xc7cc3fffffe70000

def z755 : W := mkw 0xf7c649036b540000 0x63ef8c9206d6a800 0xffe70007fffe005f 0xbfffce000ffffc00

def z756 : W := mkw 0xffeeedb269140000 0x63ffdddb64d22800 0xfffffff87c7e007f 0x7ffffffff0f8fc00

def z757 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc78fffe3f7 0xff0e3e1f8f1fffc7

def z758 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xff7ffff800000026 0x47fefffff0000000

def z759 : W := mkw 0x0011124c90a9b7dc 0x0c0022249921536f 0x000000000001ff80 0x00000000000003ff

def z760 : W := mkw 0xffeeedb004004820 0x43ffdddb60080090 0xfffffff80c001c3f 0x57fffffff0180038

def z761 : W := mkw 0x50155006dc01d860 0x12a02aa00db803b0 0xe0177007f001fc02 0x87c02ee00fe003f8

def z762 : W := mkw 0x002000d8042a6da2 0x00004001b00854db 0x19e001f80c7fffdd 0x7833c003f018ffff

def z763 : W := mkw 0x85131b4592e1b358 0x050a26368b25c366 0x871fffc783e1fff7 0xef0e3fff8f07c3ff

def z764 : W := mkw 0x0011124ffff9fffc 0x1c0022249ffff3ff 0x00000007fff9ffc0 0xb80000000ffff3ff

def z765 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfff7fff80000001a 0x47ffeffff0000000

def z766 : W := mkw 0xffeeedb123540000 0x63ffdddb6246a800 0xffffffff83fe007f 0xefffffffff07fc00

def z767 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xffffffffff80007f 0xf7ffffffffff0000

def z768 : W := mkw 0xa7822d2123500000 0x014f045a4246a000 0xe79ffffff3f8007f 0xffcf3fffffe7f000

def z769 : W := mkw 0xffeeedb123540000 0x63ffdddb6246a800 0xfffffff80ffe007f 0x7ffffffff01ffc00

def z770 : W := mkw 0x50111006d8019040 0x02a022200db00320 0xf81ff007fc01fc6f 0xb7f03fe00ff803f8

def z771 : W := mkw 0x2291362cb19996d4 0x0845226c5963332d 0x669ffe3c7399fffb 0xdccd3ffc78e733ff

def z772 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x67f0fe3c73ff1ffb 0xd8cfe1fc78e7fe3f

def z773 : W := mkw 0x7aeeedb000000000 0x42f5dddb60000000 0x79fffff80000003d 0x44f3fffff0000000

def z774 : W := mkw 0x8d2eedb102400000 0x411a5ddb62048000 0x871fffff83e00077 0xef0e3fffff07c000

def z775 : W := mkw 0x083bbffc94abfffe 0x0c10777ff92957ff 0x001ffff80001ffa0 0x44003ffff00003ff

def z776 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xfffffffff3e0007f 0xefffffffffe7c000

def z777 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffffc7000007f 0xd7fffffff8e00000

def z778 : W := mkw 0xff8eed2000000000 0x03ff1dda40000000 0xff9ffff80000003f 0x47ff3ffff0000000

def z779 : W := mkw 0x504000036b540000 0x22a0800006d6a800 0x18600007fffe0040 0xb830c0000ffffc00

def z780 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xfe1ffe07fc01fc7f 0xf7fc3ffc0ff803f8

def z781 : W := mkw 0xf7c464236b540000 0x63ef88c846d6a800 0xffe07007fffe005f 0xbbffc0e00ffffc00

def z782 : W := mkw 0xa7f33db6dc01d860 0x514fe67b6db803b0 0x07e00ffffc01fc50 0xf00fc01ffff803f8

def z783 : W := mkw 0x2280362831981694 0x0845006c5063302d 0x6680fe3873991ff9 0x58cd01fc70e7323f

def z784 : W := mkw 0x72c000036b540000 0x22e5800006d6a800 0xf8e00007fffe004f 0xbbf1c0000ffffc00

def z785 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x801ffff800000027 0x47003ffff0000000

def z786 : W := mkw 0xa7a22ff923fa279e 0x0d4f445ff247f44f 0x07e00ff803fe0390 0x480fc01ff007fc07

def z787 : W := mkw 0xafeeedb000000000 0x415fdddb60000000 0x061ffff800000020 0x440c3ffff0000000

def z788 : W := mkw 0xf7e66db000000000 0x43efccdb60000000 0xe6177ff800000002 0x47cc2efff0000000

def z789 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe80007ffffe07f 0xbbffd0000fffffc0

def z790 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x7e90fe3c7f991fff 0xf8fd21fc78ff323f

def z791 : W := mkw 0x082eedb004004820 0x40105ddb60080090 0x181ffff80c01fc6d 0x74303ffff01803f8

def z792 : W := mkw 0xffeeedb34a440000 0x63ffdddb66948800 0xfffffffffc66007f 0xf7fffffffff8cc00

def z793 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81ff007fc01ffff 0xfff03fe00ff803ff

def z794 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81ff007fc01fc2a 0x97f03fe00ff803f8

def z795 : W := mkw 0x8d6eedb000000000 0x411adddb60000000 0x017ffff800000020 0x4402fffff0000000

def z796 : W := mkw 0xdd0edb435ee07b38 0x17ba1db686bdc0f6 0x7f00ffc07fe01f98 0x58fe01ff80ffc03f

def z797 : W := mkw 0xffe880db6f7e6da2 0x23ffd101b6defcdb 0xe60881fff381ffa2 0xc3cc1103ffe703ff

def z798 : W := mkw 0x583dd096dc03d862 0x12b07ba12db807b0 0xf87ff007fc07fc6f 0xb7f0ffe00ff80ff8

def z799 : W := mkw 0x7afde6f582e1a358 0x46f5fbcdeb05c346 0x78e0f03f83e1e3c8 0xa8f1c1e07f07c3c7

def z800 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc783e1e3b2 0xcf0e3e1f8f07c3c7

def z801 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0xe69ffe3c73991fff 0xdfcd3ffc78e7323f

def z802 : W := mkw 0xa7c000036b540000 0x214f800006d6a800 0x1fe00007fffe005d 0xb83fc0000ffffc00

def z803 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x011ffff800000035 0x44023ffff0000000

def z804 : W := mkw 0xffeeedb24c004820 0x53ffdddb64980090 0xfffffff80c00003f 0x47fffffff0180000

def z805 : W := mkw 0xffeeedb248040000 0x63ffdddb64900800 0xfffffff80c06003f 0x47fffffff0180c00

def z806 : W := mkw 0x50155006dc01d860 0x12a02aa00db803b0 0xe017f007fc01fc6b 0xb7c02fe00ff803f8

def z807 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xffffffffff9e003f 0xd7ffffffffff3c00

def z808 : W := mkw 0xf7c024236b540000 0x23ef804846d6a800 0xffe00e3ffffe005f 0xfbffc01c7ffffc00

def z809 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x19fffff80c7e007d 0x7c33fffff018fc00

def z810 : W := mkw 0xffeeedb021100000 0x43ffdddb60422000 0xfffffff87018003f 0x57fffffff0e03000

def z811 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xe01ff007fc01fc62 0xb7c03fe00ff803f8

def z812 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e801f80c7fffd4 0x7833d003f018ffff

def z813 : W := mkw 0xf7c209036b540000 0x23ef841206d6a800 0xffef01c7fffe005f 0xbfffde038ffffc00

def z814 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xe69ffff80000003b 0x47cd3ffff0000000

def z815 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff800011c7f 0x57fffffff0000238

def z816 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf91ff1c7fc01fc7f 0xf7f23fe38ff803f8

def z817 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc383e1e3b4 0x6f0e3e1f8707c3c7

def z818 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xfffffffff3fe003f 0xcfffffffffe7fc00

def z819 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3c7fff1ffb 0xf8cd21fc78fffe3f

def z820 : W := mkw 0x85131b4592e1b358 0x050a26368b25c366 0xe71f7fc7f3e1e3f7 0xefce3eff8fe7c3c7

def z821 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xfffffff87ffe003f 0x5ffffffff0fffc00

def z822 : W := mkw 0x0010120c108916d0 0x000020241821122d 0x6690fe3c73991ffb 0xd8cd21fc78e7323f

def z823 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc78381e3b7 0xc70e3e1f8f0703c7

def z824 : W := mkw 0xffeeedb269140000 0x63ffdddb64d22800 0xfffffffc7f9e007f 0xdffffffff8ff3c00

def z825 : W := mkw 0xffeeedb34a400000 0x43ffdddb66948000 0xffffffffffe0007f 0xffffffffffffc000

def z826 : W := mkw 0x22d0362c319d16d4 0x2845a06c58633a2d 0x66f0fe3c739f1ffb 0xd8cde1fc78e73e3f

def z827 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x87ff0fc783ffe3f7 0xef0ffe1f8f07ffc7

def z828 : W := mkw 0xf7c024236b540000 0x23ef804846d6a800 0xfff07e07fffe005f 0xbbffe0fc0ffffc00

def z829 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xfffffffbfc7e003f 0x77fffffff7f8fc00

def z830 : W := mkw 0x85030b4182e0a318 0x050a06168305c146 0x871f0fc383e0e3b7 0x6f0e3e1f8707c1c7

def z831 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xf9e00007fffe004c 0xbbf3c0000ffffc00

def z832 : W := mkw 0x72d30b46e9b5a358 0x26e5a6168dd36b46 0x78ff0fc07c1fe3a8 0x54f1fe1f80f83fc7

def z833 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81ff007fc01fc26 0xa7f03fe00ff803f8

def z834 : W := mkw 0xffeeedb269140000 0x63ffdddb64d22800 0xfffffffffc1e007f 0xf7fffffffff83c00

def z835 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80018007f 0x5ffffffff0003000

def z836 : W := mkw 0x85030b4182e0a318 0x050a06168305c146 0x870f0fc383e1e3f5 0x6f0e1e1f8707c3c7

def z837 : W := mkw 0xf7c66d68042a6da2 0x43ef8cdad00854db 0xe6177e000c7fffc2 0x3fcc2efc0018ffff

def z838 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0xe71fffc783e1e3ff 0xefce3fff8f07c3c7

def z839 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x1ff88ff80c7fffff 0x783ff11ff018ffff

def z840 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x99ff81f80c7fffff 0x7f33ff03f018ffff

def z841 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81ff007fc7ffc6f 0xbff03fe00ff8fff8

def z842 : W := mkw 0xa7e22ff923f8279c 0x4d4fc45ff247f04f 0x07e00ff803f80390 0x480fc01ff007f007

def z843 : W := mkw 0xafeeedb000000000 0x415fdddb60000000 0x1ffffff80000003d 0x443ffffff0000000

def z844 : W := mkw 0xf7d33f27fbd5925c 0x2fefa67e4ff7ab24 0xe6177e07f3800002 0x87cc2efc0fe70000

def z845 : W := mkw 0xf7c22d236b540000 0x63ef845a46d6a800 0xffe00e07fffe005f 0xbbffc01c0ffffc00

def z846 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xfe1ff007ff81fc7f 0xbffc3fe00fff03f8

def z847 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x7ef0fe3c7f9f1ffb 0xd8fde1fc78ff3e3f

def z848 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xe01ff007f001fc6b 0x97c03fe00fe003f8

def z849 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6798fffc73991fff 0xd8cf31fff8e7323f

def z850 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6610fe3c73811ff3 0xc8cc21fc78e7023f

def z851 : W := mkw 0xafeeedb000000000 0x415fdddb60000000 0x67fffff80000003b 0x44cffffff0000000

def z852 : W := mkw 0x72c000036b540000 0x22e5800006d6a800 0x79e00007fffe005d 0xb8f3c0000ffffc00

def z853 : W := mkw 0xffeeedb34a440000 0x63ffdddb66948800 0xfffffffb8c7e007f 0x7ffffffff718fc00

def z854 : W := mkw 0x85131b4592e1b358 0x050a26368b25c366 0x871f0fc7f3e1fff7 0xff0e3e1f8fe7c3ff

def z855 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x1fe881fc0fffffff 0xf83fd103f81fffff

def z856 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x879f0fc783f9e3ff 0xff0f3e1f8f07f3c7

def z857 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xff600007fffe0046 0xbbfec0000ffffc00

def z858 : W := mkw 0xa7e66db000000000 0x414fccdb60000000 0x07f77ff800000010 0x440feefff0000000

def z859 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x01fffff800000030 0x4403fffff0000000

def z860 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x061ffff800000033 0x440c3ffff0000000

def z861 : W := mkw 0xafeeedb123540000 0x615fdddb6246a800 0x07fffff803fe0030 0x4c0ffffff007fc00

def z862 : W := mkw 0x581dd206dc81da70 0x12b03ba40db903b4 0xf81ffe07fc01ffef 0xf7f03ffc0ff803ff

def z863 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3c73991faa 0xd0cd21fc78e7323f

def z864 : W := mkw 0xffeeedb269100000 0x43ffdddb64d22000 0xffffffffff98007f 0xffffffffffff3000

def z865 : W := mkw 0xf7c024236b540000 0x23ef804846d6a800 0xffe0f03ffffe005f 0xbbffc1e07ffffc00

def z866 : W := mkw 0x2aaeedb000000000 0x40555ddb60000000 0x661ffff800000022 0x44cc3ffff0000000

def z867 : W := mkw 0x582eedb000000000 0x42b05ddb60000000 0xf9fffff80000003f 0x47f3fffff0000000

def z868 : W := mkw 0x583dd096dc01d860 0x12b07ba12db803b0 0xf81ff1fffc01fc6f 0xf7f03fe3fff803f8

def z869 : W := mkw 0x081dd0049401d860 0x10103ba0092803b0 0xe01ff007f001fc6f 0xb7c03fe00fe003f8

def z870 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81ff007f001fc2f 0x87f03fe00fe003f8

def z871 : W := mkw 0xdd2fc9d3ce62e92a 0x17ba5f93a79cc5d2 0x996f01c38c66e004 0x2732de038718cdc0

def z872 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0x9fe00007fffe0054 0xbb3fc0000ffffc00

def z873 : W := mkw 0xffeeedb269140000 0x63ffdddb64d22800 0xfffffff87000003f 0x47fffffff0e00000

def z874 : W := mkw 0x586eedb000000000 0x42b0dddb60000000 0x187ffff800000020 0x4430fffff0000000

def z875 : W := mkw 0x2280242821180480 0x0045004850423009 0x6690fe3c73991ffb 0xd8cd21fc78e7323f

def z876 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f8fc783e1ffff 0xff0e3f1f8f07c3ff

def z877 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6698fe3c7399ffff 0xf8cd31fc78e733ff

def z878 : W := mkw 0x00266db000000000 0x40004cdb60000000 0x00177ff800000000 0x44002efff0000000

def z879 : W := mkw 0x083fdbdc94abfffa 0x14107fb7b92957ff 0x001ffff80001ffa0 0x44003ffff00003ff

def z880 : W := mkw 0x500000036b540000 0x22a0000006d6a800 0xf9e00007fffe005f 0xbbf3c0000ffffc00

def z881 : W := mkw 0x582eedb000000000 0x42b05ddb60000000 0x981ffff800000024 0x47303ffff0000000

def z882 : W := mkw 0x580dd002dc00d820 0x12b01ba005b801b0 0xf81ff003fc00fc2f 0x37f03fe007f801f8

def z883 : W := mkw 0x7280000269100000 0x02e5000004d22000 0xffe00007fffe005f 0xbbffc0000ffffc00

def z884 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf91ff007fc61fc7f 0xbff23fe00ff8c3f8

def z885 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80c66003f 0x67fffffff018cc00

def z886 : W := mkw 0x8d2eedb000000000 0x411a5ddb60000000 0x9ffffff80000003f 0x473ffffff0000000

def z887 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf89ff03ffc01fc7f 0xf7f13fe07ff803f8

def z888 : W := mkw 0xdd2eedb000000000 0x43ba5ddb60000000 0xff1ffff80000003f 0x47fe3ffff0000000

def z889 : W := mkw 0xffeeedb123540000 0x63ffdddb6246a800 0xfffffff80380003f 0x47fffffff0070000

def z890 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x79f8f1f80c7fffff 0x78f3f1e3f018ffff

def z891 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xfff00e07fffe007f 0xfbffe01c0ffffc00

def z892 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xe01ff007f001fc67 0xa7c03fe00fe003f8

def z893 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3873991fb8 0x58cd21fc70e7323f

def z894 : W := mkw 0xffeeedb248000000 0x43ffdddb64900000 0xfffffffffc7e007f 0xfffffffffff8fc00

def z895 : W := mkw 0xdd6eedb000000000 0x43badddb60000000 0x9f7ffff800000037 0x473efffff0000000

def z896 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6680fe3c73991fd8 0xd8cd01fc78e7323f

def z897 : W := mkw 0xffeeedb021100000 0x43ffdddb60422000 0xfffffffc7ffe007f 0xfffffffff8fffc00

def z898 : W := mkw 0x22822d2000000000 0x0045045a40000000 0x669ffff80000003b 0x44cd3ffff0000000

def z899 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xfffffffff398007f 0xdfffffffffe73000

def z900 : W := mkw 0xdd6eedb000000000 0x43badddb60000000 0x801ffff800000020 0x47003ffff0000000

def z901 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80001e07f 0x67fffffff00003c0

def z902 : W := mkw 0x50155006dc01d860 0x12a02aa00db803b0 0xf8177007fc01fc4f 0xb7f02ee00ff803f8

def z903 : W := mkw 0x7aace4b000000000 0x02f559c960000000 0xfffffff80000003f 0x47fffffff0000000

def z904 : W := mkw 0x72c000036b540000 0x22e5800006d6a800 0x7ee00007fffe005b 0xb8fdc0000ffffc00

def z905 : W := mkw 0x0011124d92e9b7dc 0x0c0022249b25d36f 0x0000000783e1ffc0 0xa80000000f07c3ff

def z906 : W := mkw 0x850000036b540000 0x210a000006d6a800 0x9fe00007fffe005f 0xbb3fc0000ffffc00

def z907 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x9f7f0fc78fe7e3f7 0xef3efe1f8f1fcfc7

def z908 : W := mkw 0xffeeedb102400000 0x43ffdddb62048000 0xffffffff8ffe007f 0xffffffffff1ffc00

def z909 : W := mkw 0x85130b0480818250 0x010a261609010304 0x871f0fc78381e3f7 0xef0e3e1f8f0703c7

def z910 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xfee00007fffe004a 0xbbfdc0000ffffc00

def z911 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x861f0fc783e1e3e2 0xef0c3e1f8f07c3c7

def z912 : W := mkw 0xd54000036b540000 0x23aa800006d6a800 0xf9600007fffe004f 0xbbf2c0000ffffc00

def z913 : W := mkw 0x00111006dc01d860 0x100022200db803b0 0xe01ff007fc01fc6f 0xb7c03fe00ff803f8

def z914 : W := mkw 0xffeeedb102440000 0x63ffdddb62048800 0xfffffff80066003f 0x47fffffff000cc00

def z915 : W := mkw 0x583dd096dc01d860 0x12b07ba12db803b0 0xf9fff1fffc7ffc7f 0xfff3ffe3fff8fff8

def z916 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0x7ffffff800000038 0x44fffffff0000000

def z917 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81f7007fc01fc46 0xb7f03ee00ff803f8

def z918 : W := mkw 0xdd2ec99000000000 0x03ba5d9320000000 0xfffffff80000003f 0x47fffffff0000000

def z919 : W := mkw 0x8d2eedb000000000 0x411a5ddb60000000 0x861ffff800000022 0x470c3ffff0000000

def z920 : W := mkw 0x2291262ca19986d4 0x0845224c5943330d 0x869f0e3f8399e3f7 0xef0d3e1c7f0733c7

def z921 : W := mkw 0x581dd206dc81da70 0x12b03ba40db903b4 0xfe1ffe07ff81fc6f 0xb7fc3ffc0fff03f8

def z922 : W := mkw 0xf7e66db000000000 0x43efccdb60000000 0xe7ff7ff800000037 0x47cffefff0000000

def z923 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x197ffff800000024 0x4432fffff0000000

def z924 : W := mkw 0xd54000036b540000 0x23aa800006d6a800 0x99e00007fffe005d 0xbb33c0000ffffc00

def z925 : W := mkw 0xf7e66db36b540000 0x63efccdb66d6a800 0xe7f77ffff3fe0012 0xcfcfeeffffe7fc00

def z926 : W := mkw 0x7aeeedb269140000 0x62f5dddb64d22800 0x78fffff87c1e0028 0x54f1fffff0f83c00

def z927 : W := mkw 0xf7c22d2000000000 0x03ef845a40000000 0xfffffff80000003f 0x47fffffff0000000

def z928 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x879f8fff83e1e3ff 0xef0f3f1fff07c3c7

def z929 : W := mkw 0xffeeedb24c004820 0x43ffdddb64980090 0xfffffffffc01fc7f 0xf7fffffffff803f8

def z930 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe00007ffff03ff 0xfbffc0000ffffe07

def z931 : W := mkw 0x7aeeedb000000000 0x42f5dddb60000000 0x601ffff800000020 0x44c03ffff0000000

def z932 : W := mkw 0xdd6fc9d3ce60e928 0x57badf93a79cc1d2 0x996f01c38c60e004 0x2732de038718c1c0

def z933 : W := mkw 0xffeeedb004004820 0x43ffdddb60080090 0xfffffff80c7ffc7f 0x7ffffffff018fff8

def z934 : W := mkw 0xffeeedb123540000 0x63ffdddb6246a800 0xfffffffc73fe007f 0xdffffffff8e7fc00

def z935 : W := mkw 0x8d2eedb000000000 0x411a5ddb60000000 0x811ffff800000024 0x47023ffff0000000

def z936 : W := mkw 0x85022d2000000000 0x010a045a40000000 0x871ffff800000037 0x470e3ffff0000000

def z937 : W := mkw 0xffeeedb004004820 0x43ffdddb60080090 0xfffffff80c00e03f 0x67fffffff01801c0

def z938 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x9f1f0fc78fe1e3ff 0xff3e3e1f8f1fc3c7

def z939 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x870f0fc783e1e3d4 0xef0e1e1f8f07c3c7

def z940 : W := mkw 0x581dd206dc81da70 0x12b03ba40db903b4 0xf81ff007ff81ffef 0xbff03fe00fff03ff

def z941 : W := mkw 0xa791124db3f9b7dc 0x0d4f22249b67f36f 0xe7800007f3f9ffdf 0xbbcf00000fe7f3ff

def z942 : W := mkw 0x2280362831981694 0x0845006c5063302d 0x6690fe3873981fbb 0x58cd21fc70e7303f

def z943 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x861f0fc78381e3e7 0xe70c3e1f8f0703c7

def z944 : W := mkw 0x0011124cb1b9b7dc 0x0c0022249963736f 0x000000047399ffc0 0x9800000008e733ff

def z945 : W := mkw 0x2280362831981694 0x0845006c5063302d 0x6680fe3c73981fdb 0xd8cd01fc78e7303f

def z946 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf89ff007fc19fc7f 0xbff13fe00ff833f8

def z947 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf97ff007fc67fc6f 0xb7f2ffe00ff8cff8

def z948 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe08007ffff1c7f 0xbbffc1000ffffe38

def z949 : W := mkw 0x083df6fc94abfff6 0x18107bedf92957ff 0x001ffff80001ffa0 0x44003ffff00003ff

def z950 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfe1ffff80000002f 0x47fc3ffff0000000

def z951 : W := mkw 0xffeeedb248000000 0x43ffdddb64900000 0xfffffffb8c00003f 0x67fffffff7180000

def z952 : W := mkw 0x0011024480a1a350 0x0000220489014346 0x871f0fc783e1e3f7 0xef0e3e1f8f07c3c7

def z953 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3c73991fca 0x98cd21fc78e7323f

def z954 : W := mkw 0x081990049401d860 0x00103320092803b0 0xf81ff007fc01fc6f 0xb7f03fe00ff803f8

def z955 : W := mkw 0x0011124fdeebfffa 0x140022249fbdd7ff 0x00000007ffffffc0 0xb80000000fffffff

def z956 : W := mkw 0xdd6eedb000000000 0x43badddb60000000 0xf97ffff80000002f 0x47f2fffff0000000

def z957 : W := mkw 0x85030b4182e0a318 0x050a06168305c146 0x870f0fc783e0e3d7 0xef0e1e1f8f07c1c7

def z958 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffffc0380007f 0xcffffffff8070000

def z959 : W := mkw 0xd54000036b540000 0x23aa800006d6a800 0x9f600007fffe0057 0xbb3ec0000ffffc00

def z960 : W := mkw 0x2291362cb19996d4 0x0845226c5963332d 0x6690fe3ff399fffb 0xf8cd21fc7fe733ff

def z961 : W := mkw 0x2aeeedb000000000 0x4055dddb60000000 0x00fffff800000020 0x4401fffff0000000

def z962 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x99e881ff8c7fffff 0xfb33d103ff18ffff

def z963 : W := mkw 0xffeeedb021140000 0x63ffdddb60422800 0xfffffff8001e003f 0x47fffffff0003c00

def z964 : W := mkw 0x7aeeedb000000000 0x42f5dddb60000000 0xf8fffff80000002f 0x47f1fffff0000000

def z965 : W := mkw 0x581dd00490019040 0x02b03ba009200320 0xf81ff007f001fc6f 0xb7f03fe00fe003f8

def z966 : W := mkw 0xdd6eedb000000000 0x43badddb60000000 0x99fffff80000003d 0x4733fffff0000000

def z967 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3c73981f9a 0xd8cd21fc78e7303f

def z968 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc783e1e3a6 0xe70e3e1f8f07c3c7

def z969 : W := mkw 0xa780000123500000 0x014f00000246a000 0xffe00007fffe005f 0xbbffc0000ffffc00

def z970 : W := mkw 0xf7e66db000000000 0x43efccdb60000000 0xfff77ff80000001f 0x47ffeefff0000000

def z971 : W := mkw 0x580dd002dc00d820 0x12b01ba005b801b0 0xf80ff007fc00fc4f 0xb7f01fe00ff801f8

def z972 : W := mkw 0x580dd002dc00d820 0x12b01ba005b801b0 0xf80ff003fc01fc6d 0x37f01fe007f803f8

def z973 : W := mkw 0x2291362cb19996d4 0x0845226c5963332d 0xe697fe3ff3991ffb 0xdfcd2ffc7fe7323f

def z974 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e881f80c7fffb4 0x6833d103f018ffff

def z975 : W := mkw 0xffeeedb34a440000 0x63ffdddb66948800 0xffffffff8fe6007f 0xefffffffff1fcc00

def z976 : W := mkw 0x00022d2000000000 0x0000045a40000000 0x001ffff800000020 0x44003ffff0000000

def z977 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80060007f 0x6ffffffff000c000

def z978 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3c73991fb2 0xc8cd21fc78e7323f

def z979 : W := mkw 0x082eedb004004820 0x40105ddb60080090 0x001ffff80001fc20 0x44003ffff00003f8

def z980 : W := mkw 0xffeeedb123500000 0x43ffdddb6246a000 0xfffffffff3f8007f 0xffffffffffe7f000

def z981 : W := mkw 0xffeeedb34a440000 0x63ffdddb66948800 0xfffffffb8000003f 0x47fffffff7000000

def z982 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xe71ffff800000037 0x47ce3ffff0000000

def z983 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6690fe3c73811fbb 0xc0cd21fc78e7023f

def z984 : W := mkw 0x2290362410811250 0x0045206c48210224 0x6690fe3c73811ffb 0xd8cd21fc78e7023f

def z985 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xe7fffff800000032 0x47cffffff0000000

def z986 : W := mkw 0x85530b4582e5a358 0x250aa6168b05cb46 0x877f0fc783e7e3f7 0xef0efe1f8f07cfc7

def z987 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e081f80c7fffd8 0x7833c103f018ffff

def z988 : W := mkw 0xf7c66d2000000000 0x43ef8cda40000000 0xe79ffff80000003f 0x47cf3ffff0000000

def z989 : W := mkw 0xafaeedb000000000 0x415f5ddb60000000 0xe79ffff80000003f 0x47cf3ffff0000000

def z990 : W := mkw 0xdd6ec9d34e666922 0x63badd93a69cccd2 0x996f01c38c66e004 0x2732de038718cdc0

def z991 : W := mkw 0xd50000034a400000 0x03aa000006948000 0xffe00007fffe005f 0xbbffc0000ffffc00

def z992 : W := mkw 0xffeeedb36f544820 0x63ffdddb66dea890 0xfffffffffffffc7f 0xfffffffffffffff8

def z993 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe801c7fffe007f 0xfbffd0038ffffc00

def z994 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e881f80c7fffb8 0x5833d103f018ffff

def z995 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff8000103ff 0x4ffffffff0000207

def z996 : W := mkw 0xf7c66d236b540000 0x63ef8cda46d6a800 0xffff7fc7fffe007f 0xfffffeff8ffffc00

def z997 : W := mkw 0xafeeedb000000000 0x415fdddb60000000 0x87fffff800000037 0x470ffffff0000000

def z998 : W := mkw 0xf7e66db36b540000 0x63efccdb66d6a800 0xfff77ffffffe005f 0xffffeefffffffc00

def z999 : W := mkw 0x587dd096dc01d860 0x52b0fba12db803b0 0xf87ff007fc01fc6f 0xb7f0ffe00ff803f8

def z1000 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf817f007fc01fc4a 0xb7f02fe00ff803f8

def z1001 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6610fe3c73991fe2 0xd8cc21fc78e7323f

def z1002 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81ff007fc00fc0e 0xb7f03fe00ff801f8

def z1003 : W := mkw 0x7aecf4ba7d185ca4 0x5af5d9e974fa30b9 0x78e0f0387c181c08 0x10f1c1e070f83038

def z1004 : W := mkw 0xa7c22f6923fc279c 0x2d4f845ed247f84f 0x07e00ff803fe0390 0x480fc01ff007fc07

def z1005 : W := mkw 0x00130b4480a1a358 0x0400261689014346 0x861f0fc78381e3f7 0xef0c3e1f8f0703c7

def z1006 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf81ff003fc01fc2c 0x37f03fe007f803f8

def z1007 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xfffffffb8ffe003f 0x6ffffffff71ffc00

def z1008 : W := mkw 0x585dd006dc05d860 0x32b0bba00db80bb0 0xf87ff007fc07fc6f 0xb7f0ffe00ff80ff8

def z1009 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x9fff0fc783e1e3ff 0xef3ffe1f8f07c3c7

def z1010 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e881f80c7fffcc 0x3833d103f018ffff

def z1011 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xffff7ff800000016 0x47fffefff0000000

def z1012 : W := mkw 0xffeeedb248000000 0x43ffdddb64900000 0xfffffffff000003f 0xc7ffffffffe00000

def z1013 : W := mkw 0x082880d8042a6da2 0x00105101b00854db 0x19e881f80c7fffac 0x7033d103f018ffff

def z1014 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff8007e003f 0x4ffffffff000fc00

def z1015 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x601ffff80000002b 0x44c03ffff0000000

def z1016 : W := mkw 0x2aaeedb000000000 0x40555ddb60000000 0x609ffff800000028 0x44c13ffff0000000

def z1017 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x009ffff800000039 0x44013ffff0000000

def z1018 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe0803ffffe007f 0xfbffc1007ffffc00

def z1019 : W := mkw 0xffeeedb021100000 0x43ffdddb60422000 0xfffffffc7380003f 0xc7fffffff8e70000

def z1020 : W := mkw 0x2aaeedb000000000 0x40555ddb60000000 0x069ffff800000030 0x440d3ffff0000000

def z1021 : W := mkw 0xffeeedb248000000 0x43ffdddb64900000 0xfffffff87c00003f 0x57fffffff0f80000

def z1022 : W := mkw 0xf7e66db000000000 0x43efccdb60000000 0xe7f7fff80000003b 0x47cfeffff0000000

def z1023 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x871f0fc783e0e396 0xef0e3e1f8f07c1c7

def z1024 : W := mkw 0xf7c66d236b540000 0x63ef8cda46d6a800 0xfff7fe3ffffe007f 0xffffeffc7ffffc00

def z1025 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0xe71f0fc7f3e1e3ff 0xffce3e1f8fe7c3c7

def z1026 : W := mkw 0x583dd096dc01d860 0x12b07ba12db803b0 0xf97ff1c7fc01fc6f 0xb7f2ffe38ff803f8

def z1027 : W := mkw 0xffeeedb102400000 0x43ffdddb62048000 0xffffffff8380003f 0xc7ffffffff070000

def z1028 : W := mkw 0x228000036b540000 0x2045000006d6a800 0x7fe00007fffe005f 0xb8ffc0000ffffc00

def z1029 : W := mkw 0x582eedb000000000 0x42b05ddb60000000 0xe01ffff800000022 0x47c03ffff0000000

def z1030 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe00007fffe0016 0xabffc0000ffffc00

def z1031 : W := mkw 0xf7d1124ffbfdb7dc 0x2fefa2249ff7fb6f 0xffe00007ffffffdf 0xbbffc0000fffffff

def z1032 : W := mkw 0xdd6eedb34a440000 0x63badddb66948800 0x997ffffb8c660024 0x6732fffff718cc00

def z1033 : W := mkw 0xffeeedb36b540000 0x63ffdddb66d6a800 0xffffffffffe6003f 0xe7ffffffffffcc00

def z1034 : W := mkw 0x85130b4582e1a358 0x050a26168b05c346 0x861f0fc78381e3f3 0xcf0c3e1f8f0703c7

def z1035 : W := mkw 0x582eedb248000000 0x42b05ddb64900000 0xf81ffffffc00006f 0xf7f03ffffff80000

def z1036 : W := mkw 0x7aacf4ba7d1a5ca6 0x1af559e974fa34b9 0x78e0f0387c1e1c08 0x10f1c1e070f83c38

def z1037 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xfff0f007fffe007f 0xbbffe1e00ffffc00

def z1038 : W := mkw 0xa7e22db000000000 0x414fc45b60000000 0xe7fffff80000003f 0x47cffffff0000000

def z1039 : W := mkw 0xffeeedb102400000 0x43ffdddb62048000 0xfffffff803e0003f 0x4ffffffff007c000

def z1040 : W := mkw 0xf7c000036b540000 0x23ef800006d6a800 0xffe00007fffe000e 0xb3ffc0000ffffc00

def z1041 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfefffff80000002a 0x47fdfffff0000000

def z1042 : W := mkw 0x082eedb000000000 0x40105ddb60000000 0x18fffff800000028 0x4431fffff0000000

def z1043 : W := mkw 0x0011124efdbbfff6 0x180022249dfb77ff 0x00000007ffffffc0 0xb80000000fffffff

def z1044 : W := mkw 0x581dd006dc01d860 0x12b03ba00db803b0 0xf9fff007fc01fc7f 0xb7f3ffe00ff803f8

def z1045 : W := mkw 0x000000036b540000 0x2000000006d6a800 0x19600007fffe0044 0xb832c0000ffffc00

def z1046 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0x9ffffff800000034 0x473ffffff0000000

def z1047 : W := mkw 0xffeeedb004004820 0x43ffdddb60080090 0xfffffff80001fc3f 0x47fffffff00003f8

def z1048 : W := mkw 0xffeeedb102400000 0x43ffdddb62048000 0xfffffffb8060003f 0x67fffffff700c000

def z1049 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xffffffff8000007f 0xe7ffffffff000000

def z1050 : W := mkw 0xffeeedb000000000 0x43ffdddb60000000 0xfffffff80c00007f 0x77fffffff0180000

def z1051 : W := mkw 0x85121b4512e13358 0x050a24368a25c266 0x6710ffc473e11ffb 0xd8ce21ff88e7c23f

def z1052 : W := mkw 0x2290362c319916d4 0x0845206c5863322d 0x6790fe3c73f91fff 0xf8cf21fc78e7f23f

def z1053 : W := mkw 0xf7c209036b540000 0x23ef841206d6a800 0xfff70e07fffe005f 0xbfffee1c0ffffc00

def z1054 : W := mkw 0x50155006d8019040 0x12a02aa00db00320 0xe01ff007f001fc6f 0xb7c03fe00fe003f8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z7]),(0,[z0,z1,z8,z2,z4,z9,z5]),(0,[z0,z1,z10,z2,z11,z5,z6])],[(0,[z12,z1,z2,z13,z4,z5,z6]),(0,[z0,z1,z2,z4,z14,z5,z6]),(0,[z0,z15,z1,z2,z4,z5,z16]),(0,[z0,z1,z17,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z18]),(0,[z19,z0,z1,z2,z20,z5,z6]),(0,[z21,z0,z22,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z23,z6]),(0,[z0,z1,z4,z24,z5,z25,z6])],[(0,[z0,z1,z2,z4,z26,z5,z6]),(1,[z0,z1,z2,z4,z27,z5]),(0,[z0,z1,z2,z4,z28,z5,z6]),(0,[z29,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z30,z5,z6]),(0,[z31,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z32])],[(0,[z0,z1,z2,z4,z27,z5,z6]),(0,[z0,z1,z2,z33,z4,z5,z6]),(0,[z0,z1,z2,z34,z4,z5,z6])],[(0,[z0,z1,z35,z2,z4,z5,z6]),(0,[z36,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z37,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z5,z6])],[(0,[z39,z0,z1,z2,z4,z5,z6]),(0,[z40,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z41,z42]),(0,[z43,z0,z1,z2,z4,z5,z6]),(0,[z44,z0,z1,z2,z4,z5,z6]),(0,[z21,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z45,z0,z1,z2,z4,z5,z6]),(0,[z46,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z48,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z5,z5])],[(0,[z49,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z41,z50]),(0,[z0,z1,z2,z4,z5,z51,z6])],[(0,[z52,z0,z1,z2,z4,z5,z6]),(0,[z0,z53,z1,z54,z4,z5,z6]),(0,[z0,z55,z1,z2,z4,z5,z6]),(0,[z21,z0,z56,z2,z4,z5,z6])],[(0,[z57,z0,z1,z2,z4,z5,z6]),(0,[z58,z0,z1,z2,z4,z5,z6]),(0,[z49,z1,z59,z2,z4,z5,z6]),(0,[z60,z0,z1,z2,z4,z5,z61]),(0,[z0,z1,z2,z4,z5,z62,z6]),(0,[z0,z1,z2,z4,z63,z5,z6]),(0,[z0,z64,z1,z2,z4,z5,z6]),(0,[z0,z1,z65,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z66,z5,z6]),(0,[z0,z67,z1,z2,z4,z5,z6])],[(0,[z68,z0,z1,z2,z4,z5,z6]),(0,[z69,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z70,z6]),(0,[z0,z1,z2,z4,z5,z61,z41]),(0,[z71,z0,z72,z2,z4,z5,z6]),(0,[z0,z1,z2,z73,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z74]),(0,[z0,z1,z2,z4,z5,z6,z41]),(0,[z0,z75,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z76,z6]),(0,[z0,z1,z77,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z78,z6]),(0,[z79,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z80,z5,z6]),(0,[z81,z0,z1,z2,z4,z5,z41])],[(0,[z0,z1,z2,z4,z5,z82,z6]),(0,[z83,z0,z1,z2,z4,z5,z6]),(0,[z84,z0,z1,z2,z4,z5,z6]),(0,[z85,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z86]),(0,[z21,z0,z1,z10,z4,z5,z6]),(0,[z0,z87,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z6]),(0,[z88,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z89,z4,z5,z6]),(0,[z0,z1,z2,z4,z61,z90,z6]),(0,[z0,z1,z2,z4,z91,z5,z6])],[(0,[z0,z1,z2,z92,z4,z5,z6]),(0,[z0,z1,z2,z93,z4,z5,z6])],[],[(0,[z0,z94,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z90,z6]),(0,[z95,z0,z96,z2,z4,z5,z6]),(0,[z0,z1,z97,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z98,z5,z6]),(0,[z99,z0,z1,z2,z73,z5,z6]),(0,[z0,z100,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z101,z5])],[(0,[z0,z102,z1,z2,z4,z5,z6])],[(0,[z52,z1,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z104,z5,z6]),(0,[z0,z1,z2,z105,z4,z5,z6]),(0,[z0,z1,z2,z106,z4,z5,z6]),(0,[z0,z1,z2,z107,z4,z5,z6])],[(0,[z19,z0,z1,z2,z108,z5,z6]),(0,[z0,z1,z2,z109,z4,z5,z6])],[(0,[z0,z1,z2,z110,z4,z5,z6]),(0,[z0,z1,z2,z4,z111,z5,z6]),(1,[z0,z1,z2,z4,z112,z6]),(1,[z0,z1,z2,z4,z113,z41])]],
   [[(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z59,z4,z5,z25,z6]),(0,[z0,z1,z115,z2,z4,z5,z41])],[(0,[z116,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z13,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z117]),(0,[z0,z1,z2,z11,z4,z5,z41]),(0,[z0,z1,z118,z2,z4,z5,z6]),(0,[z119,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z120,z2,z4,z5,z6])],[(0,[z121,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z122,z4,z5,z6])],[(0,[z0,z1,z2,z4,z123,z5,z6])],[(1,[z60,z1,z2,z4,z5,z42]),(0,[z124,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z125]),(0,[z0,z1,z2,z4,z5,z6,z126]),(0,[z0,z15,z1,z2,z127,z4,z5])],[(0,[z0,z1,z2,z4,z5,z128,z6]),(0,[z129,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z130,z6]),(1,[z0,z1,z2,z4,z5,z7]),(0,[z0,z1,z2,z131,z4,z5,z6])],[(0,[z36,z0,z1,z2,z4,z5,z61]),(0,[z0,z72,z1,z2,z4,z27,z5]),(0,[z0,z1,z2,z4,z132,z5,z6])],[(0,[z52,z0,z133,z2,z4,z5,z6]),(0,[z0,z133,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z134,z6]),(0,[z0,z1,z2,z4,z135,z5,z6]),(0,[z0,z1,z136,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z4,z137,z5,z6]),(0,[z0,z138,z1,z2,z4,z139,z6]),(0,[z21,z0,z1,z2,z4,z5,z41]),(0,[z140,z0,z15,z1,z2,z4,z5])],[(0,[z0,z1,z141,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z142,z5,z41]),(0,[z0,z1,z2,z143,z4,z5,z6]),(0,[z0,z53,z144,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z66,z5]),(0,[z0,z145,z1,z2,z4,z5,z6])],[(0,[z0,z146,z1,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z24,z5]),(0,[z0,z1,z2,z4,z147,z5,z6]),(0,[z148,z0,z1,z2,z4,z5,z41])],[(0,[z0,z15,z133,z1,z2,z4,z5]),(0,[z1,z2,z13,z4,z47,z5,z6]),(0,[z0,z1,z2,z4,z66,z5,z61])],[(0,[z0,z1,z2,z54,z4,z5,z41])],[(0,[z0,z1,z149,z2,z4,z5,z6]),(1,[z19,z1,z2,z4,z76,z6]),(0,[z150,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z151,z2,z4,z5,z6]),(0,[z0,z1,z2,z152,z4,z5,z6]),(0,[z0,z1,z2,z73,z4,z5,z41]),(1,[z0,z15,z1,z2,z4,z41])],[(0,[z153,z0,z1,z2,z4,z5,z6]),(0,[z154,z0,z2,z54,z4,z5,z6]),(0,[z155,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z156,z6]),(0,[z157,z0,z1,z2,z4,z5,z6]),(0,[z158,z0,z1,z2,z4,z5,z74]),(0,[z158,z0,z1,z2,z4,z5,z41])],[(0,[z52,z159,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z160]),(0,[z161,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z162,z6]),(0,[z0,z1,z2,z163,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z164]),(0,[z0,z1,z8,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z165])],[(0,[z166,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z167,z5,z6]),(0,[z0,z168,z1,z2,z4,z142,z5]),(0,[z0,z1,z2,z4,z169,z5,z6]),(0,[z0,z1,z2,z170,z5,z6,z74])],[(0,[z0,z1,z171,z2,z4,z5,z6]),(0,[z71,z0,z15,z1,z2,z4,z5]),(0,[z99,z0,z15,z1,z2,z4,z5]),(0,[z0,z1,z172,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z24,z5,z41]),(0,[z0,z173,z15,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z174,z5,z6]),(0,[z0,z1,z2,z4,z5,z175,z6]),(0,[z0,z1,z2,z127,z5,z113,z6])],[(0,[z12,z0,z15,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z176,z6]),(0,[z0,z1,z2,z4,z177,z5,z6]),(0,[z0,z1,z178,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z179,z5,z6]),(0,[z180,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z170,z4,z5,z41]),(0,[z0,z1,z181,z2,z4,z5,z41]),(0,[z0,z15,z1,z2,z4,z6,z41])],[(0,[z159,z0,z15,z1,z2,z4,z5]),(0,[z182,z0,z1,z2,z4,z5,z6]),(0,[z183,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z184,z6]),(0,[z0,z1,z2,z127,z73,z4,z6])]],
   [[(0,[z0,z185,z1,z2,z4,z5,z6]),(0,[z186,z0,z15,z1,z2,z4,z5]),(0,[z0,z1,z187,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z188]),(0,[z0,z15,z72,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z16]),(0,[z0,z189,z1,z2,z4,z5,z6])],[(0,[z0,z138,z1,z2,z190,z4,z5]),(0,[z191,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z192,z4,z5,z6]),(0,[z0,z1,z2,z193,z4,z5,z6]),(0,[z194,z0,z1,z2,z4,z5,z6])],[(0,[z0,z195,z1,z2,z4,z5,z6]),(0,[z0,z196,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z197,z4,z24,z5])],[(0,[z0,z1,z2,z4,z198,z5,z6]),(0,[z199,z0,z1,z2,z4,z5,z6]),(0,[z60,z0,z15,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z200,z6]),(0,[z0,z1,z2,z4,z201,z5,z6])],[(0,[z0,z1,z2,z202,z4,z5,z6]),(0,[z0,z138,z1,z2,z4,z203,z5])],[(0,[z204,z0,z1,z2,z4,z5,z6]),(0,[z205,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z10,z144,z4,z5,z6]),(0,[z0,z72,z2,z4,z5,z206,z6])],[(0,[z0,z1,z2,z4,z5,z61,z6]),(0,[z0,z1,z2,z207,z4,z5,z6]),(0,[z95,z0,z2,z4,z208,z5,z6]),(0,[z0,z1,z2,z209,z4,z5,z6])],[(0,[z81,z0,z1,z2,z4,z5,z6]),(0,[z0,z210,z1,z2,z4,z5,z6]),(0,[z0,z96,z2,z54,z4,z5,z6]),(0,[z0,z15,z1,z2,z54,z4,z5]),(0,[z0,z72,z1,z2,z4,z5,z125]),(0,[z0,z1,z11,z4,z28,z5,z6]),(0,[z211,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z212,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z213,z4,z5,z6]),(0,[z0,z1,z2,z4,z214,z5,z6])],[(0,[z215,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z216,z4,z5,z6]),(0,[z0,z1,z2,z127,z4,z5,z217])],[(0,[z148,z0,z1,z2,z4,z113,z6]),(0,[z218,z0,z1,z2,z4,z5,z6])],[(0,[z0,z103,z2,z4,z5,z206,z6]),(0,[z186,z0,z1,z2,z4,z5,z219]),(0,[z0,z1,z2,z220,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z221,z6]),(0,[z0,z1,z222,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z223,z5,z6]),(0,[z71,z0,z1,z2,z4,z206,z6]),(0,[z71,z0,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z224,z6]),(0,[z0,z1,z10,z11,z4,z5,z6])],[(0,[z0,z1,z225,z2,z4,z5,z6]),(0,[z60,z0,z1,z2,z4,z5,z42]),(0,[z0,z53,z1,z144,z4,z5,z6]),(0,[z0,z96,z1,z2,z208,z5,z6]),(0,[z0,z1,z2,z4,z226,z5,z6])],[(0,[z19,z0,z1,z2,z4,z142,z6]),(0,[z0,z1,z2,z4,z5,z6,z227]),(0,[z0,z1,z2,z73,z4,z113,z6])],[(0,[z69,z0,z1,z2,z13,z5,z6]),(0,[z228,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z229,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z230,z5,z6]),(0,[z0,z1,z2,z4,z5,z42,z50]),(0,[z0,z1,z2,z231,z4,z5,z6]),(0,[z0,z1,z2,z232,z4,z5,z6]),(0,[z0,z1,z2,z4,z233,z5,z6]),(0,[z0,z1,z2,z4,z234,z6,z41])],[(0,[z0,z1,z2,z235,z4,z5,z6]),(0,[z236,z0,z1,z2,z4,z5,z6]),(0,[z0,z53,z1,z2,z4,z5,z6]),(0,[z0,z1,z237,z2,z4,z5,z6]),(0,[z0,z1,z2,z238,z4,z5,z6]),(1,[z71,z0,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z239,z6])]],
   [[(0,[z240,z0,z1,z2,z4,z5,z41]),(0,[z241,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z115,z4,z5,z6,z50])],[(0,[z0,z1,z2,z4,z242,z5,z6]),(0,[z0,z1,z243,z2,z4,z5,z6]),(0,[z0,z1,z244,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z245,z5,z6]),(0,[z0,z1,z2,z4,z246,z5,z6]),(0,[z0,z1,z2,z127,z4,z6,z41]),(0,[z0,z1,z2,z170,z190,z4,z5]),(0,[z0,z1,z2,z4,z247,z5,z41]),(0,[z248,z0,z15,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z249,z5,z6]),(0,[z0,z1,z2,z250,z4,z5,z6]),(0,[z0,z1,z2,z4,z251,z5,z6]),(0,[z0,z1,z252,z4,z5,z25,z6]),(0,[z0,z1,z2,z4,z253,z5,z6]),(1,[z99,z0,z1,z2,z127,z6])],[(0,[z36,z60,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z11,z4,z5,z6]),(0,[z0,z1,z10,z2,z28,z5,z6]),(0,[z254,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z219,z6]),(1,[z0,z1,z255,z4,z5,z6]),(0,[z154,z0,z15,z1,z2,z4,z5]),(0,[z0,z72,z1,z2,z4,z5,z41])],[(0,[z256,z0,z1,z2,z4,z5,z6]),(1,[z0,z257,z2,z4,z5,z6]),(0,[z0,z1,z258,z2,z4,z5,z6])],[(0,[z0,z1,z10,z54,z4,z5,z6]),(0,[z0,z15,z1,z2,z259,z4,z5]),(0,[z0,z1,z2,z260,z4,z5,z6])],[(0,[z0,z261,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z262]),(0,[z0,z1,z2,z208,z28,z5,z6]),(0,[z0,z15,z1,z2,z4,z208,z5]),(0,[z0,z1,z2,z4,z263,z5,z6]),(0,[z0,z15,z15,z1,z2,z4,z5])]],
   [[(0,[z71,z0,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z264]),(0,[z0,z138,z1,z2,z4,z5,z6]),(0,[z265,z0,z1,z2,z4,z5,z41]),(0,[z148,z0,z15,z1,z2,z4,z6]),(0,[z0,z266,z1,z2,z4,z5,z6])],[(0,[z0,z133,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z267,z4,z5,z41]),(0,[z0,z1,z2,z4,z268,z5,z6]),(0,[z0,z1,z2,z4,z5,z269,z6]),(0,[z270,z0,z1,z2,z4,z5,z41]),(0,[z0,z22,z1,z2,z4,z5,z6])],[(0,[z133,z1,z103,z2,z4,z5,z6]),(0,[z271,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z272,z6])],[(0,[z0,z1,z273,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z142,z5,z6]),(0,[z0,z1,z144,z4,z28,z5,z6]),(0,[z0,z1,z2,z4,z274,z5,z6]),(0,[z275,z0,z1,z2,z4,z5,z6]),(0,[z276,z0,z1,z2,z4,z5,z6])],[(0,[z19,z0,z1,z2,z4,z5,z6]),(0,[z154,z0,z53,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z277,z6]),(0,[z0,z1,z2,z4,z5,z6,z278]),(0,[z0,z1,z2,z279,z4,z5,z6]),(0,[z148,z0,z1,z2,z4,z5,z6])],[(0,[z159,z0,z103,z2,z4,z5,z6]),(0,[z280,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z281,z4,z5,z6]),(0,[z0,z1,z282,z2,z4,z5,z6])],[(0,[z283,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z267,z4,z5,z6,z50]),(0,[z0,z1,z2,z284,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z285,z6]),(0,[z0,z1,z2,z54,z4,z5,z6]),(1,[z286,z0,z1,z4,z24,z6])],[(0,[z0,z1,z2,z4,z5,z287,z6]),(0,[z1,z59,z2,z267,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z5,z206]),(0,[z0,z138,z1,z2,z4,z112,z6])]],
   [[(0,[z0,z15,z1,z2,z4,z5,z42]),(0,[z158,z0,z1,z2,z4,z5,z6])],[(0,[z288,z0,z1,z2,z4,z5,z6]),(0,[z289,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z41,z41])],[(0,[z0,z1,z2,z11,z259,z5,z6]),(0,[z0,z15,z1,z2,z4,z5,z50])],[(0,[z0,z133,z2,z4,z5,z206,z6]),(0,[z0,z15,z1,z2,z4,z5,z76]),(0,[z0,z1,z2,z290,z4,z5,z6]),(0,[z0,z1,z291,z2,z4,z5,z6]),(0,[z0,z1,z252,z2,z4,z5,z292]),(0,[z0,z1,z2,z4,z293,z5,z6]),(0,[z0,z294,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z295,z5,z6])],[(0,[z296,z0,z1,z2,z4,z5,z6]),(0,[z0,z297,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z298,z6])],[(0,[z0,z1,z299,z2,z4,z5,z6]),(1,[z124,z0,z1,z2,z4,z6]),(1,[z0,z53,z144,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z5,z6]),(1,[z0,z1,z2,z197,z4,z5])],[(0,[z0,z1,z2,z300,z4,z5,z6]),(0,[z0,z1,z2,z301,z4,z5,z6]),(0,[z0,z15,z53,z1,z2,z4,z5]),(0,[z302,z0,z1,z2,z4,z5,z6]),(0,[z303,z0,z1,z2,z4,z5,z6])],[(0,[z304,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z305,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z306]),(0,[z286,z0,z1,z2,z4,z25,z6])]],
   [[(1,[z49,z1,z59,z4,z5,z6]),(0,[z154,z0,z1,z2,z307,z5,z6]),(0,[z0,z53,z1,z2,z4,z5,z41]),(0,[z308,z0,z1,z2,z4,z5,z6]),(0,[z286,z0,z1,z252,z4,z5,z6]),(0,[z309,z0,z1,z2,z4,z5,z6]),(0,[z310,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z170,z4,z5,z6]),(0,[z0,z1,z181,z2,z4,z5,z6])],[(1,[z0,z1,z2,z311,z4,z5]),(0,[z119,z0,z15,z1,z2,z4,z5])],[],[(0,[z312,z0,z1,z2,z4,z5,z6]),(0,[z240,z0,z1,z2,z4,z142,z6]),(0,[z0,z1,z2,z313,z4,z5,z6])],[(0,[z0,z1,z2,z4,z314,z5,z6]),(0,[z270,z0,z1,z2,z190,z4,z5])],[(0,[z0,z315,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z316,z5,z6]),(0,[z0,z1,z2,z4,z203,z5,z41]),(0,[z0,z1,z317,z2,z4,z5,z6]),(1,[z0,z1,z115,z4,z5,z50]),(0,[z0,z318,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z319,z4,z5,z6])],[(0,[z60,z0,z1,z320,z4,z5,z6]),(0,[z0,z1,z2,z4,z321,z5,z6])],[(0,[z322,z0,z1,z267,z4,z5,z6]),(0,[z0,z15,z1,z59,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z2,z4,z5,z323,z6]),(0,[z324,z0,z1,z2,z4,z5,z6]),(0,[z270,z0,z1,z2,z4,z203,z5])]],
   [[(0,[z325,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z326,z5,z6]),(0,[z148,z0,z1,z2,z127,z4,z6])],[(0,[z0,z1,z257,z2,z4,z5,z6]),(0,[z19,z148,z0,z1,z2,z4,z6]),(0,[z0,z15,z1,z144,z2,z4,z5]),(0,[z0,z138,z1,z2,z4,z5,z41])],[(1,[z240,z0,z1,z2,z4,z41]),(0,[z95,z0,z1,z163,z4,z5,z6]),(0,[z327,z0,z1,z2,z4,z5,z6]),(0,[z286,z0,z15,z1,z2,z4,z5])],[(0,[z0,z1,z2,z47,z5,z113,z6]),(0,[z0,z1,z2,z4,z5,z6,z328]),(0,[z329,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z330,z6]),(0,[z0,z331,z15,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z6,z332])],[(0,[z19,z0,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z333,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z334]),(0,[z0,z335,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z336,z4,z5,z6]),(0,[z0,z1,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z112,z6]),(0,[z0,z1,z252,z2,z4,z25,z6]),(0,[z0,z15,z1,z115,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z113,z41]),(0,[z158,z0,z1,z2,z170,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z338]),(0,[z0,z1,z2,z4,z339,z5,z6]),(0,[z0,z1,z2,z4,z340,z5,z6]),(0,[z0,z1,z2,z341,z4,z5,z6]),(0,[z0,z1,z2,z4,z234,z5,z41])]],
   [[(0,[z342,z0,z1,z2,z4,z5,z6])],[(1,[z52,z103,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z13,z4,z5]),(0,[z0,z15,z1,z343,z2,z4,z5])],[(0,[z322,z0,z1,z59,z4,z5,z6]),(0,[z240,z0,z1,z2,z4,z5,z6])],[(0,[z0,z344,z1,z2,z4,z5,z6]),(0,[z345,z0,z1,z2,z4,z5,z6]),(1,[z158,z0,z1,z2,z170,z5]),(0,[z0,z1,z2,z4,z247,z5,z6])],[(0,[z0,z1,z2,z4,z5,z346,z6]),(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z0,z15,z1,z10,z2,z4,z5]),(0,[z348,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z349,z41])],[(0,[z0,z1,z2,z4,z5,z6,z350]),(0,[z186,z0,z1,z2,z4,z5,z351]),(0,[z0,z2,z54,z4,z208,z5,z6]),(0,[z0,z1,z2,z4,z352,z5,z6]),(0,[z353,z0,z15,z1,z2,z4,z5])],[(0,[z0,z1,z2,z13,z5,z113,z6]),(0,[z0,z1,z2,z354,z4,z5,z6]),(1,[z0,z1,z222,z4,z5,z6]),(0,[z0,z72,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z355])],[(0,[z322,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z356,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z357,z6]),(0,[z0,z1,z2,z358,z4,z5,z6])],[(0,[z0,z1,z359,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z360,z5,z6]),(0,[z0,z1,z2,z4,z361,z5,z6]),(0,[z322,z0,z1,z115,z4,z5,z6]),(0,[z362,z0,z1,z2,z4,z5,z6])],[(0,[z265,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z363,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z217])],[(0,[z0,z1,z2,z267,z4,z5,z6]),(1,[z12,z1,z2,z13,z5,z6]),(1,[z0,z1,z364,z4,z5,z6]),(0,[z270,z0,z1,z2,z4,z5,z6]),(0,[z0,z15,z138,z1,z2,z4,z5])],[(0,[z99,z0,z1,z2,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z365,z6]),(0,[z0,z1,z2,z366,z4,z5,z6]),(0,[z0,z367,z1,z2,z4,z5,z6])],[(0,[z0,z1,z368,z2,z4,z5,z6]),(1,[z0,z96,z2,z259,z5,z6]),(0,[z0,z369,z1,z2,z4,z5,z6])],[(0,[z159,z133,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z370,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z371,z6]),(0,[z0,z2,z259,z4,z208,z5,z6])],[(0,[z12,z0,z1,z2,z47,z5,z6]),(0,[z0,z1,z2,z4,z372,z5,z6]),(0,[z0,z1,z2,z4,z5,z373,z6]),(0,[z0,z1,z2,z4,z5,z374,z6]),(0,[z0,z1,z2,z4,z5,z41,z375]),(0,[z81,z0,z15,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z142,z5,z328]),(0,[z0,z1,z2,z4,z5,z376,z6]),(0,[z0,z1,z2,z4,z5,z377,z6]),(0,[z378,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z379,z2,z4,z5,z6]),(0,[z0,z1,z2,z380,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z5,z41])],[(0,[z0,z381,z1,z2,z4,z5,z6]),(0,[z0,z382,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z259,z28,z5,z6])],[(0,[z36,z1,z2,z4,z5,z61,z6]),(0,[z95,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z206,z41]),(1,[z0,z1,z2,z4,z9,z41]),(0,[z0,z1,z2,z4,z5,z41,z383]),(0,[z0,z15,z1,z2,z107,z4,z5])],[(0,[z0,z1,z2,z4,z384,z5,z6]),(1,[z44,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z208,z5,z41]),(0,[z0,z1,z10,z2,z4,z5,z6]),(0,[z385,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z386,z4,z5,z6]),(0,[z0,z1,z2,z387,z4,z5,z6]),(0,[z0,z1,z2,z388,z4,z5,z6])],[(0,[z389,z0,z1,z2,z4,z5,z6]),(0,[z71,z0,z1,z2,z4,z5,z41]),(0,[z99,z0,z1,z2,z4,z5,z41])],[(0,[z390,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z391,z4,z5,z6]),(0,[z0,z1,z2,z392,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z393,z5,z6])]],
   [[(0,[z69,z12,z1,z2,z4,z5,z6]),(0,[z12,z0,z1,z2,z4,z5,z41]),(1,[z0,z1,z2,z4,z5,z328]),(0,[z394,z0,z1,z2,z4,z5,z6]),(0,[z395,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z73,z4,z5,z396]),(0,[z0,z1,z2,z4,z397,z5,z6]),(0,[z0,z1,z343,z2,z4,z5,z6])],[(1,[z69,z1,z2,z47,z5,z6]),(0,[z0,z398,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z399,z5,z6]),(0,[z154,z0,z1,z11,z4,z5,z6]),(0,[z400,z0,z1,z2,z4,z5,z6]),(0,[z401,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z332]),(0,[z0,z1,z2,z4,z5,z6,z50]),(0,[z0,z15,z367,z1,z2,z4,z5])],[(0,[z0,z1,z2,z402,z4,z5,z6]),(0,[z159,z0,z1,z2,z4,z5,z41])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z2,z403,z4,z5,z6]),(1,[z0,z1,z2,z20,z5,z6]),(0,[z0,z1,z2,z4,z404,z5,z6]),(0,[z158,z0,z1,z2,z190,z5,z6])],[(0,[z0,z1,z2,z4,z405,z5,z6]),(0,[z406,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z396]),(0,[z0,z1,z407,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z408]),(1,[z159,z133,z2,z4,z5,z6]),(0,[z148,z240,z0,z1,z2,z4,z6]),(0,[z0,z138,z1,z2,z4,z5,z16])],[(0,[z409,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z410,z2,z4,z5,z6]),(0,[z0,z1,z411,z2,z4,z5,z6]),(0,[z0,z1,z2,z412,z4,z5,z6]),(0,[z0,z1,z2,z413,z4,z5,z6]),(0,[z29,z0,z15,z1,z2,z4,z5])],[(0,[z0,z1,z414,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z415,z5,z6]),(0,[z0,z1,z2,z259,z4,z5,z41]),(0,[z416,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z203,z5,z6]),(0,[z21,z0,z1,z4,z28,z5,z6]),(0,[z417,z0,z1,z2,z4,z5,z6]),(0,[z418,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z419,z4,z5,z6]),(0,[z420,z0,z1,z2,z4,z5,z41])]],
   [[(0,[z421,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z422,z6]),(0,[z423,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z424,z6]),(0,[z322,z0,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z356,z5,z41])],[(0,[z36,z0,z15,z1,z2,z4,z5]),(0,[z95,z0,z1,z2,z259,z5,z6]),(0,[z0,z425,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z358,z4,z5,z41])],[(0,[z0,z1,z103,z2,z4,z5,z6]),(0,[z44,z0,z1,z2,z4,z208,z5]),(0,[z21,z0,z15,z1,z2,z4,z5])],[(0,[z0,z1,z2,z426,z4,z5,z6]),(0,[z0,z1,z4,z66,z5,z6,z50])],[(0,[z49,z0,z15,z1,z2,z4,z5]),(0,[z154,z0,z1,z54,z4,z5,z6]),(0,[z99,z0,z1,z2,z127,z5,z6]),(0,[z0,z1,z2,z427,z4,z5,z6]),(0,[z148,z0,z15,z1,z2,z4,z5])],[(0,[z52,z0,z15,z1,z2,z4,z5]),(0,[z428,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z115,z2,z4,z5,z50]),(0,[z0,z1,z2,z429,z4,z5,z6])],[(0,[z0,z1,z2,z430,z4,z5,z6])],[(0,[z0,z1,z431,z2,z4,z5,z6]),(0,[z432,z0,z1,z2,z4,z5,z6]),(0,[z0,z433,z1,z2,z4,z5,z6]),(0,[z69,z0,z15,z1,z2,z4,z5]),(0,[z154,z21,z0,z1,z4,z5,z6]),(0,[z0,z2,z4,z9,z5,z206,z6]),(0,[z0,z138,z2,z4,z5,z6,z16]),(0,[z0,z15,z1,z2,z4,z5,z25]),(0,[z0,z1,z2,z434,z4,z5,z6])]],
   [[(0,[z435,z0,z1,z2,z4,z5,z6]),(0,[z436,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z437]),(0,[z0,z1,z2,z4,z438,z5,z6]),(1,[z0,z1,z2,z4,z5,z70]),(0,[z0,z1,z2,z4,z439,z5,z6]),(0,[z440,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z113,z6]),(0,[z441,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z190,z4,z442,z6]),(0,[z158,z0,z15,z1,z2,z4,z5]),(0,[z0,z15,z1,z2,z170,z4,z5])],[(0,[z49,z186,z1,z2,z4,z5,z6]),(0,[z0,z1,z443,z2,z4,z5,z6]),(0,[z1,z2,z4,z142,z5,z76,z6]),(0,[z0,z1,z2,z4,z9,z6,z41]),(0,[z0,z1,z2,z4,z234,z5,z6])],[(0,[z36,z0,z1,z2,z4,z5,z42]),(0,[z0,z1,z444,z2,z4,z5,z6])],[(1,[z0,z168,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z445,z5,z6]),(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z95,z0,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z137,z5,z6]),(0,[z0,z1,z2,z447,z4,z5,z6]),(0,[z448,z0,z1,z2,z4,z5,z6]),(1,[z0,z15,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z449,z6]),(0,[z450,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z41,z74]),(0,[z385,z0,z1,z2,z4,z5,z41])],[(0,[z0,z1,z451,z2,z4,z5,z6]),(0,[z0,z1,z452,z2,z4,z5,z6]),(0,[z69,z1,z2,z4,z47,z5,z6]),(0,[z0,z1,z2,z453,z4,z5,z6]),(0,[z0,z1,z454,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z455,z5,z6]),(0,[z99,z0,z1,z2,z4,z113,z6])],[(0,[z0,z456,z1,z2,z4,z5,z6]),(0,[z0,z457,z1,z2,z4,z5,z6]),(0,[z99,z0,z1,z2,z13,z5,z6]),(0,[z0,z458,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z349,z6])],[(0,[z0,z1,z2,z4,z66,z5,z42]),(0,[z154,z0,z1,z2,z4,z5,z41]),(0,[z459,z0,z1,z2,z4,z5,z41])]],
   [[(0,[z0,z1,z2,z4,z460,z5,z6]),(0,[z461,z0,z1,z2,z4,z5,z6]),(0,[z0,z462,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z463]),(0,[z0,z1,z2,z4,z5,z6,z217])],[(0,[z12,z0,z1,z2,z13,z5,z6]),(0,[z464,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z465,z6]),(0,[z466,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z59,z2,z4,z5,z41]),(0,[z0,z96,z2,z259,z4,z5,z6]),(0,[z0,z1,z2,z4,z467,z5,z6]),(0,[z0,z1,z252,z2,z4,z246,z5]),(0,[z0,z15,z1,z2,z4,z5,z41])],[(0,[z0,z1,z468,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z292])],[(0,[z0,z15,z1,z2,z4,z47,z5]),(0,[z0,z1,z2,z4,z5,z6,z469]),(0,[z0,z1,z470,z2,z4,z5,z6]),(0,[z471,z0,z1,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z9,z5])],[(0,[z186,z0,z1,z267,z4,z5,z6]),(0,[z472,z0,z1,z2,z4,z5,z6]),(0,[z140,z0,z1,z2,z4,z5,z6]),(0,[z148,z0,z1,z2,z4,z206,z6]),(0,[z148,z0,z1,z2,z4,z9,z6]),(0,[z473,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z219]),(1,[z19,z0,z1,z2,z4,z41]),(0,[z474,z0,z1,z2,z4,z5,z6]),(0,[z0,z475,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z476,z5,z6])],[(0,[z0,z477,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z478,z5,z6]),(0,[z0,z1,z115,z2,z4,z66,z5]),(0,[z0,z15,z1,z2,z4,z5,z113]),(1,[z0,z1,z2,z190,z5,z74])]],
   [[(0,[z479,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z35,z4,z5,z6]),(0,[z0,z1,z2,z4,z113,z6,z41])],[(0,[z186,z1,z2,z267,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z480,z6]),(0,[z0,z1,z2,z481,z4,z5,z6]),(0,[z0,z482,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z234,z41])],[(0,[z0,z1,z2,z4,z5,z6,z483]),(0,[z71,z0,z2,z4,z9,z5,z6]),(0,[z0,z1,z2,z380,z4,z5,z6])],[(0,[z0,z1,z103,z2,z4,z5,z41]),(0,[z0,z484,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z485,z5,z6]),(0,[z0,z1,z2,z364,z4,z5,z6]),(0,[z0,z15,z1,z2,z73,z4,z5])],[(0,[z0,z1,z267,z4,z5,z25,z6]),(0,[z0,z1,z2,z73,z5,z113,z6])],[(0,[z486,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z90,z6]),(1,[z154,z0,z54,z4,z5,z6]),(0,[z0,z1,z2,z4,z208,z5,z6]),(0,[z0,z1,z2,z487,z4,z5,z6]),(0,[z0,z1,z2,z488,z4,z5,z6])],[(1,[z21,z0,z1,z28,z5,z6]),(0,[z0,z1,z2,z4,z489,z5,z6]),(0,[z0,z490,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z491,z6]),(1,[z0,z1,z2,z307,z5,z6]),(0,[z0,z1,z2,z492,z4,z5,z6]),(0,[z0,z15,z96,z1,z2,z4,z5]),(0,[z71,z0,z1,z2,z4,z5,z6]),(0,[z0,z493,z1,z2,z4,z5,z6]),(0,[z99,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z186,z0,z1,z59,z4,z5,z6]),(0,[z0,z2,z4,z203,z5,z6,z16]),(0,[z0,z173,z1,z2,z4,z5,z6]),(0,[z494,z0,z1,z2,z4,z5,z6])],[(0,[z495,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z496,z5,z6])],[(0,[z497,z0,z1,z2,z4,z5,z6]),(0,[z12,z0,z1,z2,z4,z5,z6]),(0,[z240,z0,z15,z1,z2,z4,z5]),(0,[z498,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z499,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z396])],[(0,[z52,z0,z103,z2,z4,z5,z6]),(0,[z500,z0,z1,z2,z4,z5,z6]),(0,[z501,z0,z1,z2,z4,z5,z6]),(0,[z502,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z311,z4,z5,z6]),(0,[z0,z503,z1,z2,z4,z5,z6])],[(0,[z159,z0,z1,z2,z4,z5,z6]),(0,[z504,z0,z1,z2,z4,z5,z6])],[(0,[z186,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z505,z5,z6]),(0,[z0,z1,z2,z506,z4,z5,z6]),(0,[z0,z1,z2,z4,z507,z5,z6]),(0,[z0,z1,z2,z11,z208,z5,z6]),(0,[z0,z1,z2,z508,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z25,z41]),(1,[z0,z1,z2,z73,z113,z6]),(0,[z509,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z127,z4,z5,z41]),(1,[z0,z1,z2,z4,z442,z6]),(0,[z0,z15,z1,z2,z190,z4,z5]),(0,[z0,z1,z2,z4,z5,z510,z6])],[(0,[z511,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z512,z6]),(0,[z513,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z514,z6])],[(0,[z19,z0,z1,z364,z4,z5,z6])]],
   [[(0,[z60,z0,z1,z2,z4,z5,z6]),(0,[z60,z1,z2,z4,z5,z6,z42]),(0,[z270,z0,z1,z2,z4,z5,z16]),(0,[z0,z15,z1,z2,z4,z203,z5])],[(0,[z0,z1,z2,z259,z4,z5,z6]),(1,[z95,z0,z2,z208,z5,z6]),(0,[z286,z0,z1,z4,z24,z5,z6]),(0,[z420,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z515,z5,z6]),(1,[z0,z138,z2,z4,z5,z16]),(0,[z0,z1,z2,z4,z516,z5,z6]),(0,[z517,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z351]),(0,[z518,z0,z1,z2,z4,z5,z6])],[],[(0,[z519,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z163,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z28,z5]),(0,[z0,z520,z1,z2,z4,z5,z6]),(0,[z0,z521,z1,z2,z4,z5,z6])],[(0,[z0,z1,z522,z2,z4,z5,z6]),(0,[z0,z523,z1,z2,z4,z5,z6]),(0,[z0,z524,z1,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z525,z5])],[(0,[z0,z1,z2,z4,z526,z5,z6]),(0,[z0,z1,z2,z255,z4,z5,z6]),(0,[z0,z527,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z528,z5,z6]),(0,[z0,z1,z2,z4,z5,z529,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z530]),(1,[z0,z297,z2,z4,z5,z6]),(0,[z0,z1,z2,z531,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z41,z16]),(1,[z0,z1,z2,z4,z5,z292]),(0,[z532,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z533,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z534,z6]),(1,[z0,z1,z2,z4,z5,z469])],[(0,[z19,z240,z1,z2,z4,z5,z6]),(0,[z535,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z536,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z488,z4,z5])],[(0,[z0,z1,z2,z537,z4,z5,z6]),(0,[z0,z538,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z539,z6]),(0,[z99,z0,z1,z2,z127,z4,z6])],[(0,[z0,z1,z2,z4,z540,z5,z6]),(0,[z71,z0,z133,z2,z4,z5,z6]),(0,[z541,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z542,z6]),(0,[z0,z1,z2,z4,z543,z5,z6]),(1,[z0,z1,z2,z4,z246,z5])],[(0,[z0,z1,z2,z4,z5,z544,z6]),(0,[z0,z1,z2,z4,z545,z5,z6]),(0,[z0,z1,z2,z4,z5,z546,z6]),(1,[z270,z0,z2,z4,z203,z5]),(0,[z0,z1,z547,z2,z4,z5,z6])],[(0,[z248,z0,z1,z2,z4,z5,z6]),(0,[z548,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z320,z4,z5,z6]),(0,[z0,z1,z2,z4,z549,z5,z6]),(0,[z154,z0,z1,z144,z4,z5,z6]),(0,[z0,z1,z2,z4,z223,z208,z5]),(0,[z550,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z252,z4,z25,z6]),(0,[z0,z551,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z552,z5,z6]),(0,[z553,z0,z1,z2,z4,z5,z6]),(0,[z0,z72,z1,z2,z4,z9,z6]),(0,[z0,z72,z1,z2,z4,z206,z6])]],
   [[(0,[z0,z1,z2,z4,z554,z5,z6]),(0,[z0,z1,z555,z2,z4,z5,z6]),(1,[z36,z1,z2,z4,z5,z61])],[(0,[z159,z0,z133,z2,z4,z5,z6]),(0,[z49,z0,z1,z59,z4,z5,z6]),(0,[z556,z0,z1,z2,z4,z5,z6]),(0,[z459,z0,z1,z2,z4,z5,z6]),(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z557,z6]),(0,[z0,z1,z2,z558,z4,z5,z6]),(0,[z559,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z560,z4,z5,z6])],[(0,[z0,z1,z59,z4,z5,z6,z50]),(0,[z0,z1,z2,z4,z108,z5,z6]),(0,[z0,z1,z2,z4,z561,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z42])],[(0,[z0,z15,z1,z103,z2,z4,z5]),(0,[z0,z1,z2,z562,z4,z5,z6]),(0,[z0,z1,z563,z2,z4,z5,z6]),(0,[z564,z0,z1,z2,z4,z5,z6]),(0,[z0,z565,z1,z2,z4,z5,z6]),(0,[z0,z15,z1,z2,z4,z234,z5])],[(0,[z0,z1,z59,z2,z4,z5,z6]),(0,[z19,z0,z257,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z61,z50]),(0,[z0,z1,z2,z4,z5,z6,z566]),(0,[z0,z1,z2,z4,z567,z5,z6]),(0,[z0,z1,z252,z2,z4,z5,z41]),(0,[z0,z1,z2,z190,z5,z6,z74]),(0,[z148,z0,z1,z2,z4,z234,z6]),(0,[z0,z15,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z568,z6]),(0,[z0,z1,z2,z4,z569,z5,z6]),(0,[z0,z1,z2,z4,z570,z5,z6]),(0,[z0,z1,z2,z4,z571,z5,z6]),(0,[z0,z1,z252,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z41,z227])],[(0,[z0,z1,z2,z572,z4,z5,z6]),(0,[z186,z0,z1,z2,z4,z5,z41]),(0,[z573,z0,z1,z2,z4,z5,z6]),(1,[z0,z72,z2,z4,z206,z6]),(0,[z0,z1,z2,z4,z24,z5,z332]),(0,[z574,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z61,z6,z42]),(0,[z0,z15,z1,z120,z2,z4,z5]),(0,[z0,z1,z2,z4,z525,z5,z6])]],
   [[(0,[z0,z575,z1,z2,z4,z5,z6]),(0,[z0,z1,z576,z2,z4,z5,z6]),(1,[z0,z22,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z577,z5,z6]),(0,[z0,z1,z2,z578,z4,z5,z6])],[(0,[z579,z0,z1,z2,z4,z5,z6]),(0,[z60,z0,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z206,z41]),(0,[z0,z1,z580,z2,z4,z5,z6]),(0,[z0,z1,z2,z190,z4,z5,z74]),(0,[z0,z1,z2,z190,z4,z5,z41])],[(0,[z581,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z139,z5,z6])],[(0,[z582,z0,z1,z2,z4,z5,z6]),(1,[z186,z1,z267,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z583]),(0,[z0,z1,z144,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z584,z5,z6]),(0,[z0,z585,z1,z2,z4,z5,z6]),(0,[z586,z0,z1,z2,z4,z5,z6]),(0,[z587,z0,z1,z2,z4,z5,z41])],[(0,[z19,z0,z1,z2,z4,z5,z70]),(0,[z0,z1,z2,z4,z588,z5,z6]),(0,[z0,z1,z4,z137,z208,z5,z6]),(0,[z589,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z590,z5,z6]),(0,[z322,z0,z1,z2,z4,z66,z5])],[(0,[z0,z1,z2,z4,z591,z5,z6]),(0,[z0,z1,z2,z311,z73,z4,z5])],[(0,[z592,z0,z1,z2,z4,z5,z6]),(0,[z593,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z594,z5,z6]),(0,[z0,z1,z2,z595,z4,z5,z6]),(0,[z270,z0,z2,z4,z203,z5,z6]),(0,[z0,z1,z596,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z597,z5,z6]),(0,[z286,z0,z1,z267,z4,z5,z6]),(0,[z19,z0,z15,z1,z2,z4,z5]),(0,[z0,z1,z598,z2,z4,z5,z6]),(0,[z0,z1,z54,z4,z28,z5,z6]),(0,[z21,z0,z1,z2,z11,z5,z6]),(0,[z21,z0,z1,z2,z28,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z351]),(0,[z0,z15,z1,z2,z267,z4,z5]),(0,[z154,z0,z1,z2,z301,z5,z6]),(0,[z599,z0,z1,z2,z4,z5,z6]),(1,[z0,z56,z2,z4,z5,z6])],[(0,[z0,z1,z2,z600,z4,z5,z6]),(0,[z0,z1,z2,z601,z4,z5,z6]),(0,[z602,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z603,z4,z5,z6]),(0,[z0,z1,z2,z4,z604,z5,z6]),(0,[z0,z1,z2,z4,z307,z5,z6]),(0,[z605,z0,z1,z2,z4,z5,z6]),(0,[z0,z96,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z606,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z607]),(0,[z270,z158,z0,z1,z2,z4,z5]),(0,[z608,z0,z1,z2,z4,z5,z6])],[(0,[z240,z0,z1,z2,z4,z6,z41]),(0,[z0,z1,z2,z197,z4,z5,z6]),(1,[z148,z0,z15,z1,z2,z4])],[(0,[z240,z0,z1,z2,z4,z76,z6])],[(0,[z0,z1,z609,z2,z4,z5,z6]),(0,[z0,z1,z2,z610,z4,z5,z6]),(0,[z611,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z612]),(0,[z0,z1,z2,z4,z5,z25,z6]),(0,[z0,z1,z2,z127,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z613,z6]),(0,[z614,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z615,z5,z6]),(0,[z616,z0,z1,z2,z4,z5,z6]),(0,[z0,z53,z96,z2,z4,z5,z6]),(0,[z95,z0,z1,z222,z4,z5,z6]),(0,[z270,z0,z138,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z617,z5,z6]),(0,[z0,z1,z2,z4,z5,z618,z6])],[(0,[z619,z0,z1,z2,z4,z5,z6]),(0,[z69,z0,z1,z2,z47,z5,z6]),(0,[z0,z1,z2,z4,z28,z5,z41]),(0,[z620,z0,z1,z2,z4,z5,z6]),(0,[z158,z0,z1,z2,z170,z4,z5])],[(0,[z286,z0,z1,z59,z4,z5,z6]),(1,[z0,z1,z2,z108,z5,z6]),(0,[z19,z1,z2,z4,z5,z76,z6]),(0,[z0,z1,z2,z4,z5,z621,z6]),(0,[z0,z1,z622,z2,z4,z5,z6]),(0,[z0,z1,z2,z127,z4,z101,z5]),(1,[z0,z1,z2,z412,z4,z6])],[(0,[z0,z1,z2,z623,z4,z5,z6]),(0,[z309,z0,z15,z1,z2,z4,z5])],[(0,[z19,z0,z1,z35,z4,z5,z6]),(0,[z36,z0,z1,z2,z4,z5,z41]),(0,[z0,z15,z1,z2,z4,z5,z61]),(1,[z0,z1,z2,z301,z5,z6]),(0,[z0,z1,z2,z624,z4,z5,z6])],[(0,[z0,z1,z625,z2,z4,z5,z6]),(0,[z626,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z627,z5,z6]),(0,[z628,z0,z1,z2,z4,z5,z6]),(0,[z0,z15,z1,z252,z2,z4,z5]),(0,[z0,z15,z1,z2,z4,z5,z74])],[(0,[z0,z1,z2,z4,z47,z5,z41]),(0,[z0,z629,z1,z2,z4,z5,z6]),(0,[z630,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z223,z5]),(0,[z0,z1,z2,z4,z5,z631,z6]),(1,[z0,z1,z8,z2,z4,z5]),(0,[z0,z1,z632,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z633,z6])],[(0,[z49,z0,z1,z2,z4,z5,z41]),(0,[z286,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z52,z0,z1,z2,z4,z5,z41]),(0,[z0,z331,z1,z2,z4,z5,z6]),(1,[z0,z1,z10,z11,z5,z6])],[(0,[z634,z0,z1,z2,z4,z5,z6]),(0,[z0,z96,z1,z2,z259,z5,z6]),(0,[z0,z1,z2,z4,z66,z5,z41])],[(0,[z69,z0,z1,z2,z4,z5,z41]),(0,[z0,z635,z1,z2,z4,z5,z6]),(0,[z0,z636,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z76,z41]),(0,[z0,z637,z1,z2,z4,z5,z6]),(0,[z638,z0,z1,z2,z4,z5,z6]),(0,[z0,z144,z2,z54,z4,z5,z6])],[(0,[z60,z0,z1,z255,z4,z5,z6]),(0,[z0,z1,z144,z2,z4,z5,z41]),(0,[z95,z0,z1,z2,z208,z5,z6]),(0,[z0,z1,z2,z4,z9,z5,z6])],[(0,[z0,z639,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z640,z4,z5,z6]),(0,[z0,z1,z2,z641,z4,z5,z6]),(0,[z0,z1,z2,z642,z4,z5,z6]),(0,[z0,z87,z1,z2,z4,z5,z41])],[(0,[z643,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z41])],[(0,[z0,z1,z2,z4,z5,z644,z6]),(0,[z0,z1,z645,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z646,z6]),(0,[z0,z1,z2,z4,z647,z5,z6])]],
   [[(1,[z581,z0,z1,z4,z5,z6]),(1,[z0,z1,z2,z4,z139,z6]),(0,[z648,z0,z1,z2,z4,z5,z6]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z650,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z412,z190,z4,z6]),(0,[z0,z15,z266,z1,z2,z4,z5])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z651,z4,z5,z6])],[(0,[z652,z0,z1,z2,z4,z5,z6]),(0,[z353,z0,z1,z2,z4,z5,z6])],[(0,[z653,z0,z1,z2,z4,z5,z6]),(0,[z0,z654,z1,z2,z4,z5,z6]),(0,[z0,z96,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z6,z655]),(0,[z0,z1,z2,z4,z5,z656,z6]),(0,[z0,z1,z2,z4,z657,z5,z6]),(0,[z658,z0,z1,z2,z4,z5,z6])],[(0,[z659,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z660,z5,z6]),(0,[z581,z0,z1,z4,z208,z5,z6]),(0,[z0,z1,z2,z4,z206,z6,z41]),(0,[z0,z1,z2,z4,z5,z661,z6]),(0,[z0,z1,z56,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z662,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z663]),(0,[z664,z0,z1,z2,z4,z5,z6]),(0,[z665,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z666,z5,z6])],[(0,[z0,z1,z2,z4,z667,z5,z6]),(0,[z0,z668,z1,z2,z4,z5,z6]),(0,[z0,z1,z252,z2,z4,z5,z6])],[(0,[z0,z1,z2,z13,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z6,z375]),(0,[z347,z0,z15,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z669,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z670,z6])],[(0,[z0,z1,z671,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z5,z7]),(0,[z0,z1,z2,z4,z672,z5,z6])],[(0,[z673,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z383]),(0,[z322,z0,z15,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z674,z6])],[(0,[z675,z0,z1,z2,z4,z5,z6]),(0,[z240,z1,z2,z4,z142,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z124,z0,z1,z2,z4,z61,z6]),(0,[z0,z1,z2,z4,z5,z6,z676]),(0,[z0,z1,z2,z4,z5,z206,z6]),(0,[z0,z1,z2,z190,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z677,z6])],[(0,[z19,z0,z297,z2,z4,z5,z6]),(0,[z0,z168,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z678,z6])],[(0,[z679,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z680,z5,z6]),(0,[z19,z0,z1,z2,z4,z5,z469]),(0,[z681,z0,z1,z2,z4,z5,z6]),(0,[z682,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z683,z5,z6]),(0,[z684,z0,z1,z2,z4,z5,z6]),(0,[z587,z0,z1,z2,z4,z5,z6])],[(0,[z685,z0,z1,z2,z4,z5,z6]),(0,[z270,z0,z15,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z41,z355])],[(0,[z0,z1,z320,z2,z4,z5,z6]),(0,[z322,z0,z1,z4,z66,z5,z6])]],
   [[(0,[z0,z1,z2,z686,z4,z5,z6]),(0,[z0,z1,z2,z687,z4,z5,z6]),(0,[z0,z1,z688,z2,z4,z5,z6]),(0,[z0,z1,z2,z689,z4,z5,z6]),(0,[z286,z0,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z690,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z691]),(0,[z49,z0,z1,z267,z4,z5,z6]),(0,[z19,z0,z1,z2,z4,z6,z41]),(0,[z0,z15,z1,z2,z4,z142,z5]),(0,[z21,z0,z53,z1,z4,z5,z6]),(0,[z286,z0,z1,z2,z4,z24,z6])],[(0,[z19,z0,z1,z2,z4,z76,z6]),(0,[z692,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z101,z5,z6]),(1,[z0,z1,z2,z127,z4,z41])],[(0,[z0,z1,z2,z693,z4,z5,z6]),(0,[z0,z1,z2,z694,z4,z5,z6]),(0,[z0,z1,z2,z4,z695,z5,z6]),(0,[z0,z1,z2,z4,z696,z5,z6]),(0,[z0,z697,z1,z2,z4,z5,z6]),(0,[z0,z53,z2,z4,z208,z5,z6]),(0,[z0,z1,z2,z4,z698,z5,z6])],[(0,[z699,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z700,z5,z6]),(0,[z0,z1,z2,z4,z5,z442,z6])],[(0,[z0,z1,z2,z4,z701,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z702]),(0,[z0,z1,z2,z20,z4,z5,z6]),(0,[z95,z0,z15,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z9,z5,z41]),(0,[z322,z0,z1,z2,z4,z5,z50]),(0,[z0,z1,z2,z703,z4,z5,z6])],[(0,[z704,z0,z1,z2,z4,z5,z6]),(0,[z705,z0,z1,z2,z4,z5,z6])],[(0,[z706,z0,z1,z2,z4,z5,z6]),(0,[z0,z53,z1,z11,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z125]),(0,[z158,z0,z138,z1,z2,z4,z5]),(0,[z0,z15,z1,z2,z11,z4,z5]),(0,[z0,z1,z115,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z364,z4,z5,z469]),(0,[z60,z1,z2,z4,z5,z42]),(0,[z395,z0,z54,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z125])],[(0,[z19,z0,z1,z2,z108,z41]),(0,[z573,z0,z1,z28,z5,z6]),(0,[z0,z1,z2,z4,z5,z707]),(0,[z0,z1,z2,z4,z5,z7])],[(0,[z0,z1,z243,z2,z4,z41]),(0,[z0,z1,z2,z708,z5,z6]),(0,[z0,z1,z2,z4,z439,z41])],[(0,[z140,z0,z1,z2,z4,z90]),(0,[z0,z1,z2,z301,z5,z6]),(0,[z378,z0,z1,z2,z4,z41]),(0,[z0,z709,z1,z2,z4,z5])],[(0,[z0,z1,z35,z4,z5,z70]),(0,[z0,z1,z4,z137,z5,z6]),(0,[z0,z53,z710,z4,z5,z6])],[(0,[z0,z1,z243,z4,z25,z6]),(0,[z0,z1,z8,z2,z4,z5]),(0,[z0,z1,z2,z4,z711,z6]),(0,[z0,z1,z2,z73,z113,z396])],[(0,[z712,z0,z1,z2,z4,z5]),(0,[z0,z713,z1,z2,z4,z5]),(0,[z1,z714,z2,z4,z5,z6]),(0,[z0,z96,z2,z715,z5,z6]),(0,[z0,z1,z2,z4,z716,z6])],[]],
   [[(0,[z228,z0,z1,z2,z4,z41]),(0,[z19,z0,z257,z2,z4,z41]),(0,[z0,z1,z2,z717,z5,z6]),(0,[z0,z718,z2,z4,z5,z6]),(0,[z0,z15,z1,z252,z4,z25]),(0,[z286,z0,z1,z4,z24,z41])],[(0,[z0,z1,z2,z719,z4,z5]),(0,[z0,z1,z2,z720,z4,z5]),(0,[z0,z15,z1,z2,z4,z41]),(0,[z0,z1,z181,z4,z5,z383])],[(0,[z159,z721,z2,z4,z5,z6]),(0,[z0,z1,z722,z4,z5,z6]),(0,[z0,z1,z723,z2,z4,z5]),(0,[z0,z1,z2,z4,z724,z6])],[(0,[z0,z1,z2,z47,z113,z41]),(0,[z0,z1,z2,z725,z4,z5]),(0,[z0,z1,z2,z4,z5,z726])],[(0,[z0,z1,z2,z4,z372,z41])],[(0,[z0,z1,z2,z4,z5,z41]),(1,[z721,z2,z4,z5,z6]),(0,[z727,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z728,z6]),(0,[z0,z1,z2,z4,z729,z5])],[],[(0,[z0,z297,z2,z20,z5,z6]),(0,[z0,z1,z2,z4,z139,z6]),(0,[z730,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z731,z5,z6]),(0,[z0,z1,z2,z4,z732,z6]),(0,[z733,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z90,z41])],[(0,[z0,z1,z2,z4,z734,z5]),(0,[z0,z1,z2,z4,z330,z41]),(0,[z0,z1,z735,z4,z5,z41])],[(0,[z49,z1,z59,z4,z5,z41]),(0,[z0,z1,z736,z4,z5,z6])],[(1,[z1,z2,z737,z5,z6])],[(0,[z0,z1,z2,z4,z5,z738]),(0,[z0,z1,z739,z4,z5,z6]),(0,[z532,z1,z2,z13,z5,z6]),(0,[z0,z740,z2,z4,z5,z6]),(0,[z36,z1,z2,z4,z61,z90]),(0,[z36,z1,z2,z4,z5,z349]),(0,[z0,z1,z2,z4,z112,z41])],[(0,[z0,z1,z741,z4,z5,z6]),(0,[z0,z257,z2,z4,z5,z469]),(0,[z0,z15,z1,z35,z4,z5]),(1,[z0,z1,z4,z742,z6])],[(0,[z0,z1,z743,z2,z4,z5]),(0,[z0,z53,z2,z307,z5,z6]),(0,[z744,z0,z2,z4,z5,z6]),(0,[z0,z1,z4,z745,z5,z41])],[(0,[z0,z746,z2,z4,z5,z6]),(0,[z0,z2,z4,z9,z747,z6]),(0,[z0,z2,z4,z748,z5,z16]),(0,[z0,z15,z1,z2,z4,z633])]],
   [[(0,[z0,z1,z2,z4,z749,z6]),(0,[z0,z15,z72,z2,z4,z206]),(0,[z0,z15,z1,z2,z4,z514])],[(0,[z0,z1,z2,z4,z5,z750]),(0,[z0,z1,z2,z4,z5,z751]),(0,[z752,z1,z2,z4,z5,z6]),(0,[z753,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z754,z41]),(0,[z418,z1,z2,z4,z5,z42])],[],[(0,[z0,z1,z2,z4,z755,z6]),(0,[z0,z297,z2,z4,z5,z70]),(0,[z19,z0,z1,z2,z4,z328]),(0,[z0,z1,z2,z4,z747,z6]),(1,[z0,z2,z4,z748,z5])],[(0,[z0,z1,z2,z4,z5,z756]),(0,[z0,z1,z2,z757,z5,z6]),(0,[z0,z1,z4,z137,z5,z41]),(0,[z270,z0,z596,z2,z4,z5]),(0,[z0,z15,z1,z2,z341,z4])],[(0,[z0,z1,z2,z4,z5,z758]),(0,[z0,z54,z208,z28,z5,z6]),(0,[z0,z53,z97,z4,z5,z6]),(0,[z759,z0,z1,z2,z4,z5]),(0,[z265,z0,z2,z4,z356,z5])],[]],
   [[(0,[z0,z1,z2,z4,z5,z760]),(0,[z19,z0,z1,z35,z4,z41]),(0,[z39,z0,z1,z2,z4,z41]),(0,[z154,z0,z54,z307,z5,z6]),(0,[z44,z0,z1,z4,z137,z5]),(0,[z0,z1,z2,z190,z442,z74]),(0,[z0,z1,z761,z4,z5,z6])],[(0,[z0,z1,z364,z108,z5,z6]),(0,[z762,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z127,z4,z41])],[(0,[z0,z344,z2,z4,z206,z6]),(0,[z19,z1,z2,z4,z76,z41]),(0,[z581,z0,z56,z4,z5,z6]),(0,[z0,z1,z2,z4,z529,z41])],[(0,[z0,z1,z2,z763,z5,z6]),(0,[z764,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z127,z113,z41]),(0,[z0,z1,z2,z170,z488,z5])],[(0,[z0,z1,z2,z4,z5,z765]),(0,[z0,z1,z2,z4,z5,z766])],[(0,[z0,z1,z2,z4,z5,z767]),(0,[z0,z1,z2,z4,z768,z5]),(0,[z0,z15,z1,z2,z412,z4])],[(0,[z0,z1,z2,z4,z5,z769]),(0,[z0,z1,z770,z4,z5,z6]),(0,[z0,z331,z1,z2,z4,z41]),(0,[z0,z771,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z539,z41]),(0,[z99,z0,z1,z2,z127,z6])],[(0,[z52,z15,z103,z2,z4,z5]),(0,[z0,z772,z2,z4,z5,z6]),(0,[z0,z1,z2,z773,z4,z5]),(0,[z0,z1,z2,z4,z542,z41]),(0,[z0,z2,z4,z356,z206,z41]),(0,[z158,z0,z1,z2,z4,z112]),(0,[z0,z1,z642,z4,z5,z50]),(0,[z0,z1,z2,z380,z113,z41]),(0,[z0,z1,z2,z4,z774,z41])]],
   [[(0,[z0,z1,z2,z4,z544,z41]),(0,[z0,z1,z255,z4,z5,z6]),(0,[z140,z0,z1,z2,z4,z41]),(0,[z0,z1,z222,z4,z5,z41]),(0,[z581,z0,z15,z1,z4,z5])],[(0,[z0,z775,z1,z2,z4,z6]),(0,[z240,z1,z2,z4,z142,z41])],[(0,[z649,z1,z267,z4,z5,z6]),(0,[z0,z15,z297,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z776]),(0,[z0,z1,z2,z412,z190,z74])],[(0,[z49,z1,z714,z4,z5,z6]),(0,[z0,z297,z35,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z777])],[(0,[z0,z1,z2,z13,z113,z41]),(0,[z0,z1,z364,z4,z5,z41]),(0,[z0,z1,z35,z4,z5,z469]),(0,[z587,z240,z1,z2,z4,z41])],[(0,[z1,z2,z737,z47,z5,z6]),(0,[z0,z1,z2,z4,z5,z778]),(0,[z0,z1,z779,z2,z4,z223])],[(0,[z0,z1,z2,z481,z4,z41]),(0,[z0,z1,z780,z4,z5,z6]),(0,[z0,z173,z1,z2,z488,z5])]],
   [[(0,[z0,z1,z2,z4,z781,z6]),(0,[z581,z0,z54,z4,z5,z6]),(0,[z0,z1,z4,z782,z5,z6]),(0,[z119,z248,z1,z2,z4,z5])],[(0,[z0,z783,z2,z4,z5,z6]),(0,[z0,z1,z2,z784,z4,z6])],[(0,[z286,z0,z1,z4,z24,z6])],[(0,[z60,z0,z1,z2,z4,z90]),(0,[z0,z785,z1,z2,z4,z5]),(0,[z0,z1,z2,z499,z4,z41]),(0,[z0,z1,z2,z412,z4,z101])],[(0,[z0,z1,z4,z786,z5,z6]),(0,[z60,z1,z255,z4,z5,z42]),(0,[z0,z1,z4,z742,z25,z6]),(0,[z0,z189,z1,z2,z4,z41]),(0,[z0,z1,z2,z127,z4,z774])],[(0,[z0,z1,z2,z4,z787,z5]),(0,[z19,z0,z297,z2,z4,z41]),(0,[z0,z2,z259,z715,z5,z6]),(0,[z0,z1,z2,z4,z5,z788])],[(0,[z0,z15,z1,z2,z4,z365]),(0,[z0,z1,z115,z4,z782,z5]),(0,[z0,z1,z2,z4,z424,z41])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z368,z4,z5,z50])]],
   [[(0,[z95,z0,z137,z208,z5,z6]),(0,[z0,z15,z1,z4,z137,z5]),(0,[z0,z1,z2,z4,z112,z16])],[(0,[z0,z1,z2,z4,z789,z6]),(0,[z0,z790,z2,z4,z5,z6]),(0,[z0,z791,z1,z2,z4,z5]),(0,[z124,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z792]),(0,[z0,z1,z2,z380,z5,z74])],[(0,[z0,z1,z2,z4,z104,z41]),(0,[z0,z1,z2,z4,z90,z6]),(0,[z0,z1,z2,z4,z101,z5])],[(0,[z0,z1,z793,z4,z5,z6]),(0,[z345,z0,z1,z2,z4,z41]),(0,[z0,z1,z794,z4,z5,z6]),(0,[z0,z1,z735,z4,z5,z6]),(0,[z0,z138,z2,z4,z404,z5])],[(0,[z49,z1,z59,z4,z5,z6]),(0,[z573,z0,z2,z208,z5,z6]),(0,[z0,z1,z2,z4,z795,z5]),(0,[z0,z53,z56,z4,z5,z6]),(0,[z71,z0,z2,z4,z9,z41]),(0,[z0,z1,z4,z796,z5,z6])],[(0,[z186,z1,z267,z4,z5,z219]),(0,[z19,z1,z2,z4,z797,z6])],[(0,[z0,z1,z798,z4,z5,z6]),(0,[z0,z1,z2,z108,z5,z70]),(0,[z0,z72,z2,z4,z747,z6]),(0,[z0,z1,z2,z4,z113,z41]),(0,[z158,z0,z1,z2,z799,z5])],[(0,[z0,z1,z2,z800,z5,z6]),(0,[z0,z801,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z253,z41])]],
   [[(0,[z0,z1,z4,z745,z5,z6])],[(0,[z0,z1,z255,z4,z5,z41]),(0,[z0,z138,z343,z2,z4,z5])],[(0,[z0,z103,z2,z4,z206,z41]),(0,[z0,z257,z2,z4,z5,z41]),(0,[z124,z36,z1,z2,z4,z61])],[(0,[z0,z1,z2,z4,z613,z41])],[(0,[z0,z1,z2,z4,z802,z6]),(0,[z0,z803,z1,z2,z4,z5]),(1,[z0,z2,z4,z747,z6]),(0,[z0,z1,z11,z796,z5,z6]),(0,[z140,z367,z1,z2,z4,z5])],[(0,[z0,z297,z2,z4,z5,z469]),(0,[z148,z0,z1,z2,z108,z6]),(0,[z0,z1,z2,z4,z5,z804]),(0,[z0,z1,z2,z4,z5,z805])],[(0,[z0,z1,z806,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z807]),(0,[z240,z0,z1,z2,z4,z41]),(0,[z0,z1,z2,z4,z808,z6]),(0,[z0,z1,z163,z208,z5,z6])],[(0,[z0,z809,z1,z2,z4,z5]),(0,[z286,z0,z1,z197,z4,z24])]],
   [[(0,[z0,z1,z2,z4,z5,z810])],[(0,[z0,z1,z811,z4,z5,z6]),(0,[z812,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z813,z6])],[(0,[z0,z1,z2,z4,z5,z814]),(0,[z1,z2,z13,z737,z5,z6]),(0,[z0,z15,z1,z2,z4,z112]),(0,[z0,z1,z252,z4,z25,z292]),(0,[z99,z0,z15,z1,z2,z127])],[(0,[z0,z1,z2,z4,z5,z815]),(0,[z0,z1,z816,z4,z5,z6]),(0,[z36,z0,z1,z2,z4,z90]),(0,[z0,z1,z2,z817,z5,z6])],[(0,[z0,z1,z2,z4,z5,z818]),(0,[z19,z1,z2,z4,z76,z6]),(0,[z148,z0,z257,z2,z4,z6]),(0,[z0,z819,z2,z4,z5,z6])],[(0,[z0,z1,z2,z820,z5,z6])],[(0,[z0,z1,z35,z108,z5,z6]),(0,[z0,z1,z2,z4,z5,z821])],[(0,[z0,z1,z2,z4,z480,z41]),(0,[z158,z0,z1,z2,z170,z5])]],
   [[(0,[z0,z1,z4,z223,z137,z5]),(0,[z0,z72,z2,z4,z27,z206]),(1,[z0,z1,z2,z799,z5])],[(0,[z822,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z823,z5,z6]),(0,[z0,z1,z2,z4,z5,z824]),(0,[z0,z1,z723,z2,z4,z9]),(0,[z0,z1,z2,z4,z5,z825]),(0,[z0,z1,z2,z380,z113,z6])],[(0,[z49,z15,z1,z59,z4,z5]),(0,[z124,z0,z1,z2,z4,z41]),(0,[z0,z1,z222,z4,z5,z6]),(0,[z0,z53,z144,z4,z5,z41]),(0,[z95,z581,z0,z208,z5,z6]),(0,[z21,z0,z1,z796,z5,z6]),(0,[z0,z826,z2,z4,z5,z6]),(0,[z0,z709,z1,z2,z4,z41])],[(0,[z0,z1,z2,z20,z5,z469]),(0,[z0,z1,z2,z4,z672,z41])],[(0,[z0,z1,z2,z827,z5,z6]),(0,[z0,z1,z8,z2,z4,z41])],[(0,[z0,z1,z2,z4,z828,z6]),(0,[z0,z1,z2,z4,z5,z829])],[(0,[z0,z1,z257,z2,z4,z41]),(0,[z0,z1,z2,z830,z5,z6]),(0,[z0,z2,z710,z4,z5,z6]),(1,[z0,z1,z796,z5,z6])],[(0,[z1,z721,z2,z4,z5,z6]),(0,[z0,z1,z364,z4,z5,z6]),(0,[z0,z1,z2,z4,z831,z6]),(0,[z99,z0,z1,z2,z832,z6])]],
   [[(0,[z0,z1,z833,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z834]),(0,[z0,z1,z4,z24,z742,z6])],[(0,[z19,z0,z1,z2,z4,z754]),(0,[z0,z1,z779,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z835]),(0,[z0,z1,z35,z4,z5,z41]),(0,[z0,z53,z4,z321,z5,z6])],[(0,[z0,z1,z2,z836,z5,z6]),(0,[z0,z1,z2,z481,z113,z6]),(0,[z60,z1,z2,z4,z5,z837]),(0,[z0,z1,z2,z838,z5,z6]),(0,[z839,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z728]),(0,[z840,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z190,z525,z5])],[(0,[z0,z1,z841,z4,z5,z6]),(0,[z0,z1,z4,z842,z5,z6]),(0,[z0,z1,z2,z4,z700,z41]),(0,[z0,z1,z252,z4,z246,z25])],[(0,[z0,z1,z2,z4,z9,z41]),(0,[z286,z0,z15,z1,z4,z24]),(0,[z0,z173,z1,z2,z4,z41])],[(0,[z0,z1,z2,z4,z843,z5]),(0,[z154,z0,z54,z4,z5,z41]),(0,[z44,z0,z1,z2,z4,z5]),(0,[z0,z15,z1,z10,z11,z5])]],
   [[(0,[z1,z2,z4,z5,z844,z6])],[(0,[z0,z1,z2,z4,z845,z6]),(0,[z0,z1,z846,z4,z5,z6])],[(0,[z0,z847,z2,z4,z5,z6]),(0,[z309,z0,z1,z107,z4,z5])],[(0,[z0,z1,z848,z4,z5,z6]),(0,[z0,z849,z2,z4,z5,z6]),(0,[z0,z850,z2,z4,z5,z6]),(0,[z581,z0,z1,z307,z5,z6]),(0,[z0,z2,z4,z747,z206,z6])],[(0,[z0,z1,z2,z4,z5,z328]),(0,[z0,z1,z2,z4,z851,z5])],[(0,[z69,z1,z2,z47,z5,z6]),(0,[z0,z1,z2,z852,z4,z6]),(0,[z0,z1,z2,z4,z230,z41]),(0,[z0,z1,z2,z4,z5,z332])],[(0,[z52,z103,z2,z4,z5,z41]),(0,[z0,z297,z2,z108,z5,z6]),(0,[z0,z1,z563,z11,z5,z6]),(0,[z71,z0,z2,z4,z9,z6])],[(0,[z0,z1,z2,z4,z5,z853]),(0,[z0,z398,z1,z2,z4,z41]),(0,[z12,z1,z2,z737,z5,z6]),(0,[z0,z1,z2,z108,z5,z469]),(0,[z0,z1,z2,z854,z5,z6]),(0,[z855,z1,z2,z4,z5,z6]),(0,[z0,z331,z1,z2,z4,z112])]],
   [[(0,[z0,z1,z2,z856,z5,z6]),(0,[z19,z75,z1,z2,z4,z6]),(0,[z1,z2,z4,z5,z837,z6])],[(0,[z159,z133,z2,z4,z5,z6])],[(0,[z0,z344,z1,z2,z4,z41]),(0,[z0,z2,z715,z208,z5,z6])],[(0,[z0,z1,z2,z108,z6,z41]),(0,[z95,z0,z2,z208,z5,z41])],[(0,[z0,z1,z2,z4,z857,z6]),(0,[z0,z257,z2,z4,z5,z6]),(0,[z1,z2,z4,z737,z5,z6]),(0,[z0,z15,z1,z364,z4,z5]),(0,[z19,z1,z364,z4,z76,z6]),(0,[z19,z15,z1,z2,z4,z76])],[(0,[z0,z1,z2,z4,z858,z5]),(0,[z0,z710,z54,z4,z5,z6]),(0,[z0,z1,z2,z715,z5,z6])],[(0,[z0,z859,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z63,z41]),(1,[z0,z163,z208,z5,z6]),(0,[z0,z860,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z861,z5]),(0,[z0,z1,z343,z2,z4,z41])],[(0,[z186,z1,z267,z4,z5,z351]),(0,[z240,z1,z2,z4,z349,z41]),(0,[z0,z1,z862,z4,z5,z6]),(0,[z459,z1,z2,z4,z5,z349])]],
   [[(0,[z0,z863,z2,z4,z5,z6]),(0,[z12,z1,z2,z13,z5,z41]),(0,[z0,z15,z1,z2,z301,z5]),(0,[z0,z1,z2,z4,z5,z864]),(0,[z0,z1,z2,z4,z5,z728]),(0,[z0,z1,z2,z4,z865,z6])],[(0,[z0,z1,z866,z2,z4,z5]),(0,[z0,z1,z2,z867,z4,z5]),(0,[z0,z1,z868,z4,z5,z6]),(0,[z869,z0,z1,z4,z5,z6])],[(0,[z0,z297,z2,z4,z5,z41]),(0,[z0,z1,z870,z4,z5,z6]),(0,[z0,z96,z2,z259,z5,z41])],[(0,[z0,z2,z4,z871,z5,z6]),(0,[z1,z2,z4,z5,z797,z6]),(0,[z36,z1,z2,z4,z5,z837]),(0,[z0,z1,z2,z4,z872,z6]),(0,[z71,z0,z2,z4,z9,z7])],[(0,[z133,z721,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z873]),(0,[z0,z1,z2,z4,z5,z70]),(0,[z60,z367,z1,z2,z4,z5]),(0,[z0,z1,z2,z874,z4,z5]),(0,[z0,z875,z2,z4,z5,z41])],[(0,[z0,z1,z2,z876,z5,z6]),(0,[z0,z877,z2,z4,z5,z6]),(0,[z878,z0,z1,z2,z4,z5]),(0,[z0,z96,z163,z4,z5,z6])],[(0,[z0,z879,z1,z2,z4,z6]),(0,[z0,z1,z880,z2,z4,z6]),(0,[z0,z1,z2,z881,z4,z5])],[(0,[z0,z15,z1,z2,z4,z5]),(0,[z325,z0,z1,z2,z4,z41]),(0,[z19,z0,z1,z364,z4,z41]),(1,[z0,z1,z2,z108,z41]),(0,[z0,z15,z1,z163,z4,z5]),(0,[z0,z1,z882,z4,z5,z6]),(0,[z0,z56,z4,z28,z5,z6]),(0,[z0,z1,z2,z4,z782,z5])]],
   [[(0,[z0,z1,z2,z4,z108,z41]),(0,[z0,z1,z2,z4,z525,z41])],[(0,[z0,z1,z2,z883,z4,z6]),(0,[z0,z1,z884,z4,z5,z6]),(0,[z0,z87,z2,z4,z5,z16]),(0,[z0,z1,z56,z28,z5,z6])],[(0,[z0,z1,z2,z4,z5,z885]),(0,[z71,z0,z2,z4,z460,z6]),(0,[z0,z1,z2,z4,z886,z5]),(0,[z0,z1,z2,z4,z393,z41])],[(0,[z0,z1,z887,z4,z5,z6]),(0,[z154,z0,z56,z4,z5,z6])],[(0,[z0,z53,z144,z4,z5,z6]),(0,[z0,z56,z2,z11,z5,z6]),(0,[z0,z1,z2,z4,z888,z5]),(0,[z0,z1,z2,z197,z4,z5]),(0,[z158,z0,z1,z2,z358,z5]),(0,[z0,z709,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z889]),(0,[z303,z1,z2,z47,z5,z6]),(0,[z890,z1,z2,z4,z5,z6]),(0,[z95,z0,z163,z208,z5,z6])],[(0,[z418,z1,z267,z4,z5,z6]),(0,[z69,z1,z2,z47,z5,z41]),(1,[z0,z257,z2,z4,z41]),(0,[z148,z0,z1,z2,z4,z101])],[(0,[z0,z1,z2,z4,z891,z6])]],
   [[(0,[z69,z15,z1,z2,z47,z5]),(0,[z0,z1,z892,z4,z5,z6]),(0,[z0,z1,z2,z20,z5,z41]),(0,[z650,z1,z2,z4,z5,z61]),(0,[z0,z1,z2,z311,z4,z5])],[(0,[z19,z257,z2,z4,z76,z6]),(0,[z0,z146,z144,z4,z5,z6]),(0,[z71,z0,z15,z2,z4,z9])],[(0,[z159,z133,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z219]),(0,[z0,z893,z2,z4,z5,z6])],[(0,[z0,z1,z255,z4,z5,z61]),(0,[z0,z1,z2,z190,z5,z74])],[(0,[z0,z1,z35,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z894]),(0,[z0,z1,z2,z4,z895,z5]),(0,[z0,z1,z2,z796,z5,z6]),(0,[z0,z1,z115,z4,z5,z50])],[(0,[z186,z1,z267,z4,z5,z41]),(0,[z0,z1,z299,z2,z4,z41]),(0,[z0,z896,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z234,z41])],[(0,[z0,z1,z2,z4,z5,z897]),(0,[z154,z0,z710,z4,z5,z6]),(0,[z0,z15,z1,z222,z4,z5]),(0,[z0,z1,z2,z4,z543,z41]),(0,[z0,z1,z2,z4,z742,z6]),(0,[z0,z898,z1,z2,z4,z5]),(0,[z0,z87,z2,z4,z5,z227])],[(0,[z0,z1,z2,z4,z5,z899]),(0,[z0,z1,z11,z584,z5,z6]),(0,[z0,z15,z1,z2,z4,z139])]],
   [[(0,[z0,z1,z2,z4,z900,z5]),(0,[z0,z1,z2,z4,z5,z901]),(0,[z0,z1,z2,z4,z526,z41]),(0,[z99,z0,z1,z2,z127,z217]),(0,[z0,z15,z1,z902,z4,z5])],[(0,[z0,z1,z2,z903,z4,z5]),(0,[z19,z1,z2,z4,z76,z70]),(0,[z148,z0,z1,z2,z4,z70]),(0,[z154,z0,z54,z4,z5,z6])],[(0,[z0,z1,z2,z4,z134,z41]),(0,[z0,z1,z2,z904,z4,z6]),(0,[z905,z0,z1,z2,z4,z5])],[(0,[z0,z1,z2,z906,z4,z6])],[(0,[z0,z257,z364,z4,z5,z6]),(0,[z0,z1,z2,z4,z631,z41]),(0,[z0,z1,z10,z796,z5,z6])],[(0,[z275,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z907,z5,z6]),(0,[z0,z1,z2,z4,z5,z908]),(0,[z0,z1,z2,z909,z5,z6]),(0,[z0,z96,z2,z290,z5,z6]),(0,[z0,z1,z2,z799,z4,z5])],[(0,[z0,z1,z11,z307,z5,z6])],[]],
   [[(0,[z52,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z910,z6]),(0,[z0,z1,z2,z911,z5,z6]),(0,[z0,z1,z902,z4,z5,z6]),(0,[z0,z1,z2,z4,z912,z6]),(0,[z913,z0,z1,z4,z5,z6]),(0,[z0,z15,z1,z632,z2,z4])],[(0,[z0,z1,z2,z4,z5,z914]),(0,[z0,z1,z2,z73,z113,z6]),(0,[z0,z1,z2,z4,z442,z6]),(0,[z0,z1,z915,z4,z5,z6])],[(0,[z1,z2,z4,z5,z61,z837]),(0,[z0,z2,z4,z203,z748,z5]),(0,[z0,z1,z2,z4,z5,z916]),(0,[z730,z15,z1,z2,z4,z5])],[(0,[z0,z1,z917,z4,z5,z6]),(0,[z0,z1,z2,z4,z918,z5]),(0,[z0,z1,z2,z4,z919,z5]),(0,[z0,z1,z2,z4,z797,z6]),(0,[z0,z1,z920,z4,z5,z6])],[(0,[z0,z1,z2,z108,z5,z41]),(0,[z581,z0,z1,z28,z5,z6]),(0,[z581,z0,z1,z11,z5,z6]),(0,[z0,z1,z2,z4,z9,z125]),(0,[z0,z1,z2,z4,z206,z125]),(0,[z303,z0,z1,z2,z4,z41])],[(0,[z0,z1,z921,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z922]),(0,[z0,z1,z2,z4,z644,z41]),(0,[z95,z0,z2,z208,z5,z6]),(1,[z0,z2,z715,z5,z6]),(0,[z0,z1,z2,z4,z774,z5])],[(0,[z0,z315,z1,z2,z4,z41]),(0,[z157,z1,z59,z4,z5,z6])],[(0,[z0,z923,z1,z2,z4,z5]),(0,[z159,z15,z133,z2,z4,z5]),(0,[z0,z1,z2,z4,z924,z6]),(0,[z0,z1,z2,z4,z5,z925]),(0,[z69,z1,z2,z737,z5,z6])]],
   [[(0,[z154,z0,z54,z301,z5,z6]),(0,[z0,z1,z181,z4,z5,z50]),(0,[z0,z1,z2,z926,z4,z5])],[(0,[z19,z1,z35,z4,z76,z6]),(0,[z0,z1,z54,z307,z5,z6]),(0,[z0,z1,z2,z4,z5,z217]),(0,[z0,z1,z2,z4,z113,z396])],[(0,[z12,z1,z2,z13,z5,z6]),(0,[z581,z0,z1,z4,z223,z5]),(0,[z0,z1,z2,z4,z5,z927]),(0,[z0,z1,z2,z4,z661,z41]),(0,[z0,z1,z10,z11,z5,z41])],[(0,[z0,z1,z2,z928,z5,z6]),(0,[z0,z1,z2,z4,z5,z929]),(0,[z99,z0,z1,z2,z127,z101]),(0,[z0,z1,z2,z380,z5,z355])],[(0,[z0,z1,z2,z4,z930,z6]),(0,[z0,z297,z2,z4,z5,z6]),(0,[z0,z1,z2,z931,z4,z5]),(0,[z21,z0,z1,z307,z5,z6]),(0,[z0,z96,z2,z259,z5,z6]),(0,[z0,z2,z4,z9,z206,z41]),(0,[z0,z1,z723,z2,z4,z41]),(0,[z0,z138,z2,z4,z748,z5]),(0,[z0,z2,z4,z932,z5,z6]),(0,[z0,z1,z2,z4,z5,z292]),(0,[z0,z1,z2,z4,z5,z933]),(0,[z0,z1,z2,z578,z4,z41]),(0,[z0,z67,z1,z2,z4,z41])],[(0,[z0,z1,z2,z4,z5,z469]),(0,[z240,z0,z1,z2,z4,z328]),(0,[z0,z1,z2,z4,z5,z934]),(0,[z0,z2,z163,z208,z5,z6]),(0,[z0,z1,z2,z4,z935,z5]),(0,[z0,z138,z2,z4,z112,z16]),(0,[z0,z15,z458,z1,z2,z4]),(0,[z347,z0,z343,z2,z4,z5])],[(0,[z0,z668,z1,z2,z4,z41]),(0,[z0,z875,z2,z4,z5,z6]),(0,[z0,z144,z710,z4,z5,z6]),(0,[z0,z1,z2,z936,z4,z5]),(0,[z0,z1,z2,z799,z190,z5])],[(0,[z395,z0,z2,z208,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z937]),(0,[z95,z44,z0,z2,z208,z5]),(0,[z158,z0,z1,z2,z617,z5]),(0,[z0,z1,z2,z4,z246,z5]),(0,[z0,z1,z2,z4,z674,z41]),(0,[z119,z0,z1,z2,z4,z41])],[(0,[z0,z1,z2,z938,z5,z6]),(0,[z0,z1,z2,z939,z5,z6]),(0,[z0,z1,z940,z4,z5,z6]),(0,[z0,z1,z2,z4,z941,z5]),(0,[z0,z1,z2,z4,z206,z41]),(0,[z270,z0,z2,z4,z203,z5]),(0,[z0,z942,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z677,z41])],[(0,[z0,z1,z320,z4,z5,z6]),(0,[z0,z1,z2,z943,z5,z6]),(0,[z0,z1,z2,z4,z678,z41]),(0,[z270,z0,z2,z4,z356,z5]),(0,[z944,z0,z1,z2,z4,z5])],[(0,[z21,z0,z1,z28,z5,z41]),(0,[z286,z0,z1,z4,z24,z332])],[(0,[z0,z1,z267,z4,z5,z351]),(0,[z0,z15,z1,z2,z20,z5]),(0,[z36,z1,z2,z4,z5,z61]),(0,[z0,z1,z2,z307,z5,z41]),(0,[z95,z0,z2,z715,z5,z6]),(0,[z71,z0,z8,z2,z4,z9]),(0,[z0,z945,z2,z4,z5,z6]),(0,[z762,z15,z1,z2,z4,z5])],[(0,[z0,z1,z946,z4,z5,z6]),(0,[z52,z721,z2,z4,z5,z6]),(0,[z587,z1,z2,z4,z5,z42])],[(0,[z0,z1,z947,z4,z5,z6])],[(0,[z0,z1,z2,z4,z948,z6]),(0,[z721,z103,z2,z4,z5,z6]),(0,[z0,z949,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z950]),(0,[z0,z1,z2,z4,z5,z951])]],
   [[],[(0,[z952,z0,z1,z2,z5,z6]),(0,[z0,z953,z2,z4,z5,z6]),(0,[z0,z257,z2,z4,z5,z70]),(0,[z0,z54,z4,z307,z5,z6]),(0,[z0,z15,z53,z144,z4,z5]),(0,[z0,z53,z11,z208,z5,z6]),(0,[z0,z15,z709,z1,z2,z4])],[(0,[z186,z1,z714,z4,z5,z6]),(0,[z0,z1,z2,z20,z5,z6]),(0,[z286,z0,z1,z4,z742,z6]),(0,[z0,z1,z2,z73,z113,z41]),(0,[z0,z1,z2,z4,z442,z41]),(0,[z0,z1,z2,z4,z442,z74]),(0,[z0,z1,z2,z170,z799,z5]),(0,[z0,z1,z915,z4,z5,z41])],[(0,[z954,z0,z1,z4,z5,z6]),(0,[z955,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z956,z5]),(0,[z0,z1,z2,z231,z4,z41]),(0,[z0,z1,z2,z4,z98,z41]),(0,[z0,z15,z1,z2,z4,z175]),(0,[z0,z1,z2,z4,z5,z396])],[(0,[z0,z1,z2,z957,z5,z6]),(0,[z0,z1,z2,z4,z5,z958]),(0,[z0,z1,z2,z4,z959,z6]),(0,[z0,z960,z2,z4,z5,z6]),(0,[z0,z1,z115,z107,z4,z5]),(0,[z0,z15,z1,z2,z4,z442])],[(0,[z0,z1,z2,z4,z316,z41]),(0,[z0,z1,z961,z2,z4,z5])],[(0,[z186,z15,z1,z267,z4,z5]),(0,[z0,z1,z2,z105,z4,z41]),(0,[z60,z1,z320,z4,z5,z42]),(0,[z962,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z832,z73,z6])],[(0,[z186,z1,z267,z4,z5,z6]),(0,[z0,z1,z59,z4,z5,z351]),(0,[z0,z1,z2,z4,z208,z728]),(0,[z0,z1,z2,z358,z113,z41])]],
   [[(0,[z0,z1,z2,z4,z5,z963]),(0,[z0,z1,z2,z964,z4,z5]),(0,[z0,z1,z2,z832,z5,z6])],[(0,[z19,z297,z2,z4,z76,z6]),(0,[z0,z1,z965,z4,z5,z6]),(0,[z0,z138,z2,z4,z139,z16])],[(0,[z0,z1,z2,z4,z966,z5]),(0,[z0,z967,z2,z4,z5,z6]),(0,[z19,z1,z2,z4,z76,z469]),(0,[z1,z2,z4,z797,z76,z6]),(0,[z0,z1,z163,z4,z5,z41]),(0,[z0,z1,z2,z4,z662,z41])],[(0,[z0,z15,z1,z2,z108,z5]),(0,[z0,z1,z2,z4,z203,z112])],[(0,[z0,z1,z2,z968,z5,z6]),(0,[z0,z1,z2,z4,z969,z6]),(0,[z0,z1,z2,z4,z5,z351]),(0,[z0,z1,z2,z4,z269,z41])],[(0,[z0,z1,z2,z4,z460,z41]),(0,[z0,z1,z2,z4,z5,z970]),(0,[z270,z0,z2,z4,z748,z5])],[(0,[z0,z1,z2,z4,z667,z41]),(0,[z0,z133,z2,z4,z206,z41]),(0,[z0,z635,z1,z2,z4,z41]),(0,[z0,z1,z971,z4,z5,z6]),(0,[z0,z72,z2,z4,z206,z125])],[(0,[z0,z1,z972,z4,z5,z6]),(0,[z0,z1,z2,z4,z277,z41]),(0,[z0,z1,z2,z4,z223,z728])]],
   [[(0,[z0,z1,z370,z4,z5,z50]),(0,[z148,z0,z15,z1,z2,z4])],[(0,[z0,z973,z2,z4,z5,z6]),(0,[z0,z257,z35,z4,z5,z6]),(0,[z124,z0,z1,z2,z4,z70]),(0,[z0,z15,z1,z2,z307,z5]),(0,[z974,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z975])],[(0,[z0,z168,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z70,z41]),(0,[z976,z0,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z977]),(0,[z0,z1,z320,z4,z5,z41]),(0,[z0,z1,z2,z4,z78,z41]),(0,[z0,z1,z252,z4,z25,z41]),(0,[z0,z1,z2,z4,z147,z41])],[(0,[z0,z978,z2,z4,z5,z6]),(0,[z0,z979,z1,z2,z4,z5]),(0,[z0,z1,z710,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z980]),(0,[z0,z1,z2,z333,z4,z41]),(0,[z0,z1,z252,z4,z742,z6])],[],[(0,[z0,z1,z2,z4,z5,z981]),(0,[z0,z1,z2,z108,z5,z6]),(0,[z0,z1,z2,z4,z5,z982]),(0,[z0,z1,z2,z4,z66,z90]),(0,[z0,z1,z4,z782,z5,z50]),(0,[z0,z1,z2,z412,z4,z6]),(0,[z0,z173,z1,z2,z4,z442])],[(0,[z19,z1,z2,z20,z76,z6]),(0,[z0,z983,z2,z4,z5,z6]),(0,[z0,z2,z4,z715,z5,z6]),(0,[z0,z56,z2,z28,z5,z6]),(0,[z0,z984,z2,z4,z5,z6]),(0,[z0,z1,z2,z127,z4,z396])]],
   [[(0,[z0,z331,z266,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z985]),(1,[z0,z54,z307,z5,z6]),(0,[z0,z475,z1,z2,z4,z41])],[(0,[z0,z15,z1,z255,z4,z5]),(0,[z0,z1,z2,z986,z5,z6]),(0,[z0,z1,z2,z4,z223,z5]),(0,[z148,z0,z709,z1,z2,z4])],[(0,[z0,z72,z2,z4,z206,z41])],[(0,[z0,z1,z10,z11,z5,z6]),(0,[z987,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z988]),(0,[z19,z0,z1,z2,z4,z41]),(0,[z0,z1,z2,z4,z989,z5]),(0,[z0,z22,z2,z4,z5,z41])],[(0,[z0,z2,z4,z990,z5,z6]),(0,[z0,z15,z1,z2,z4,z38]),(0,[z0,z1,z2,z388,z4,z41])],[(0,[z0,z1,z2,z4,z991,z6])]],
   [[(0,[z0,z1,z2,z4,z90,z50])],[(0,[z0,z1,z2,z4,z5,z992]),(0,[z581,z0,z53,z4,z5,z6])],[(0,[z0,z1,z2,z4,z993,z6]),(0,[z0,z1,z364,z20,z5,z6]),(0,[z994,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z130,z41]),(0,[z0,z1,z144,z307,z5,z6])],[(0,[z0,z1,z2,z4,z5,z995]),(0,[z581,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z101,z41])],[(0,[z0,z1,z2,z4,z996,z6]),(0,[z0,z56,z2,z4,z5,z41]),(0,[z0,z15,z56,z2,z4,z5]),(0,[z21,z0,z1,z28,z5,z6]),(0,[z0,z1,z2,z4,z997,z5]),(0,[z420,z0,z1,z2,z358,z5]),(0,[z0,z15,z1,z868,z4,z5])],[(0,[z0,z1,z2,z4,z5,z998]),(0,[z0,z1,z2,z307,z5,z6]),(0,[z0,z1,z999,z4,z5,z6])],[(0,[z0,z1,z1000,z4,z5,z6]),(0,[z0,z163,z4,z208,z5,z6]),(0,[z0,z2,z4,z747,z5,z6])]],
   [[(0,[z275,z0,z1,z2,z4,z41]),(0,[z0,z87,z2,z4,z206,z6])],[(0,[z0,z1001,z2,z4,z5,z6])],[(0,[z0,z1,z1002,z4,z5,z6]),(0,[z0,z1,z2,z1003,z5,z6]),(0,[z0,z1,z4,z1004,z5,z6]),(0,[z0,z1,z8,z2,z4,z139]),(0,[z587,z1,z2,z4,z5,z375])],[(0,[z19,z1,z2,z108,z76,z6]),(0,[z1005,z0,z1,z2,z5,z6]),(0,[z0,z1,z1006,z4,z5,z6])],[(0,[z119,z1,z2,z4,z5,z61])],[(0,[z658,z1,z59,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1007]),(0,[z0,z1,z1008,z4,z5,z6]),(0,[z0,z15,z22,z2,z4,z5])],[(0,[z286,z0,z1,z4,z526,z6]),(0,[z12,z15,z1,z2,z13,z5]),(0,[z0,z257,z2,z4,z6,z41])],[(0,[z0,z1,z364,z4,z5,z70]),(0,[z0,z1,z2,z412,z4,z41]),(0,[z0,z1,z2,z799,z5,z6])]],
   [[(0,[z0,z1,z2,z1009,z5,z6]),(0,[z0,z138,z1,z2,z4,z442]),(0,[z0,z1,z2,z708,z5,z41])],[(0,[z0,z1,z2,z301,z5,z41]),(0,[z0,z138,z2,z4,z5,z16])],[(0,[z1010,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z748,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1011]),(0,[z0,z1,z2,z4,z5,z1012]),(0,[z0,z1,z2,z4,z5,z837]),(0,[z1013,z1,z2,z4,z5,z6]),(0,[z401,z0,z1,z2,z4,z41]),(1,[z0,z709,z1,z2,z4])],[(0,[z0,z1,z2,z4,z5,z1014]),(0,[z0,z1015,z1,z2,z4,z5]),(0,[z0,z1,z163,z4,z5,z6]),(0,[z0,z1,z1016,z2,z4,z5])],[(0,[z0,z1017,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z1018,z6]),(0,[z0,z1,z2,z4,z5,z1019]),(0,[z0,z1,z1020,z2,z4,z5]),(0,[z148,z0,z1,z8,z2,z4]),(0,[z0,z1,z2,z4,z5,z1021]),(0,[z0,z15,z1,z2,z73,z113])],[(0,[z0,z1,z2,z4,z5,z1022]),(0,[z0,z1,z2,z717,z5,z41])],[(0,[z0,z1,z2,z1023,z5,z6]),(0,[z0,z1,z714,z4,z5,z6]),(0,[z0,z257,z2,z20,z5,z6]),(0,[z0,z15,z1,z2,z4,z376]),(0,[z21,z0,z15,z1,z28,z5]),(0,[z0,z1,z2,z832,z4,z6]),(0,[z0,z2,z4,z990,z5,z41])]],
   [[(0,[z0,z1,z2,z4,z1024,z6]),(0,[z0,z1,z688,z2,z4,z41]),(0,[z21,z0,z56,z28,z5,z6]),(0,[z0,z1,z2,z4,z263,z41])],[(0,[z1,z59,z714,z4,z5,z6]),(0,[z0,z1,z2,z4,z371,z41]),(0,[z0,z1,z2,z832,z113,z6])],[(0,[z0,z1,z2,z1025,z5,z6]),(0,[z581,z44,z0,z1,z4,z5]),(0,[z0,z1,z2,z4,z373,z41]),(0,[z0,z1,z2,z127,z832,z6])],[],[(0,[z0,z1,z1026,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1027]),(0,[z0,z1,z2,z4,z5,z754]),(0,[z0,z15,z1,z2,z4,z90]),(1,[z0,z710,z4,z5,z6]),(0,[z0,z520,z2,z259,z5,z6]),(0,[z0,z1,z2,z190,z571,z5]),(1,[z0,z56,z28,z5,z6])],[(0,[z0,z1028,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z445,z41]),(0,[z581,z0,z1,z4,z5,z41]),(0,[z0,z1,z2,z4,z139,z41]),(0,[z0,z1,z252,z4,z25,z6])],[(0,[z0,z1,z2,z1029,z4,z5]),(0,[z95,z0,z15,z2,z208,z5]),(0,[z0,z1,z2,z311,z73,z113])],[(0,[z0,z1,z2,z4,z1030,z6]),(0,[z0,z1,z2,z20,z5,z70]),(0,[z0,z1,z2,z4,z27,z5])]],
   [[(0,[z124,z0,z15,z1,z2,z4]),(0,[z0,z1,z2,z4,z5,z1031]),(0,[z0,z1,z2,z4,z1032,z5]),(0,[z0,z335,z2,z4,z9,z6]),(0,[z21,z0,z22,z28,z5,z6])],[(0,[z692,z0,z54,z4,z5,z6]),(0,[z0,z87,z2,z4,z206,z41])],[(0,[z0,z1,z2,z4,z5,z1033]),(0,[z0,z1,z2,z1034,z5,z6]),(0,[z241,z0,z1,z28,z5,z6]),(0,[z0,z1,z2,z1035,z4,z5]),(0,[z0,z709,z1,z2,z4,z234])],[(0,[z0,z1,z163,z259,z5,z6]),(0,[z0,z1,z796,z28,z5,z6]),(0,[z348,z0,z1,z2,z4,z41])],[(0,[z0,z1,z2,z1036,z5,z6]),(0,[z0,z1,z2,z4,z1037,z6]),(0,[z0,z1,z2,z4,z1038,z5]),(0,[z0,z1,z2,z4,z5,z1039])],[(0,[z0,z1,z2,z4,z1040,z6]),(0,[z0,z721,z2,z4,z5,z6]),(0,[z205,z0,z1,z2,z4,z41]),(0,[z0,z1,z2,z4,z5,z1041]),(0,[z0,z1042,z1,z2,z4,z5]),(0,[z0,z72,z2,z4,z206,z6])],[(0,[z1043,z0,z1,z2,z4,z5]),(0,[z0,z1,z1044,z4,z5,z6])],[(0,[z0,z1,z522,z4,z5,z50]),(0,[z0,z22,z2,z4,z5,z6])]],
   [[(0,[z1045,z0,z1,z2,z4,z6]),(0,[z0,z2,z54,z307,z5,z6]),(0,[z0,z1,z2,z127,z427,z6]),(0,[z0,z1,z2,z799,z5,z74])],[(0,[z0,z1,z2,z4,z567,z41]),(0,[z95,z0,z2,z223,z208,z5]),(0,[z270,z0,z1,z2,z4,z442])],[(0,[z19,z0,z1,z2,z20,z41]),(0,[z0,z15,z1,z320,z4,z5]),(0,[z0,z1,z2,z4,z5,z1046])],[(0,[z0,z1,z2,z4,z5,z1047]),(0,[z0,z1,z2,z737,z5,z6]),(0,[z0,z257,z2,z108,z5,z6]),(0,[z95,z0,z222,z208,z5,z6]),(0,[z0,z1,z2,z4,z5,z1048]),(0,[z0,z1,z2,z190,z4,z112])],[(0,[z1,z2,z4,z5,z837,z42]),(0,[z0,z1,z2,z4,z748,z5])],[(0,[z19,z240,z1,z2,z4,z41]),(0,[z518,z0,z2,z208,z5,z6]),(0,[z0,z1,z2,z170,z4,z442])],[(0,[z1,z714,z267,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1049]),(0,[z0,z1,z761,z4,z5,z41])],[(0,[z0,z1,z35,z20,z5,z6]),(0,[z0,z1,z255,z4,z5,z42]),(0,[z0,z15,z1,z2,z4,z111]),(0,[z0,z56,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z1050]),(0,[z0,z1,z10,z640,z5,z6])],[(0,[z99,z0,z1,z2,z105,z6]),(0,[z154,z0,z15,z54,z4,z5]),(0,[z353,z0,z1,z2,z525,z5])],[(0,[z0,z1,z1051,z4,z5,z6]),(0,[z71,z0,z2,z4,z747,z6])],[(1,[z1,z2,z4,z5,z837]),(0,[z0,z1,z2,z4,z112,z6])],[(0,[z0,z1,z2,z4,z285,z41]),(1,[z0,z1,z2,z832,z6]),(0,[z99,z0,z1,z2,z127,z41])],[(0,[z0,z15,z257,z2,z4,z5]),(0,[z0,z1,z2,z4,z384,z41]),(0,[z0,z15,z96,z2,z259,z5]),(0,[z0,z266,z2,z4,z203,z5])],[(0,[z564,z133,z2,z4,z5,z6]),(0,[z0,z1052,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1053,z6])],[(0,[z0,z1,z1054,z4,z5,z6]),(1,[z1,z714,z4,z5,z6]),(0,[z0,z297,z364,z4,z5,z6]),(0,[z0,z56,z10,z4,z5,z6]),(0,[z0,z1,z4,z742,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 533).take 538) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1071).take 81) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1152)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [533, 538, 81] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 134).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 134).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 253).take 3).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [134, 119, 3] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_42582

theorem PEqualNP.Outside.L_meta_42582 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42582.solve