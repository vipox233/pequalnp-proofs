import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43588

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4271959168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x020b303611ac78c9#64 ++ 0x04082cc0d846b1e3#64 ++ 0x063f707e13fcf9fe#64 ++ 0x9c18fdc1f84ff3e7#64 : BitVec 256),
   (0x08d8058b14610b52#64 ++ 0x002360162c51842d#64 ++ 0x19d89f8f1c631ffd#64 ++ 0xf467627e3c718c7f#64 : BitVec 256),
   (0x6160c2d16057a19c#64 ++ 0x0985830b45815e86#64 ++ 0xe1e0e3f1e07fe1fb#64 ++ 0xdf87838fc781ff87#64 : BitVec 256),
   (0xb600f800aa82d420#64 ++ 0x02d803e002aa0b50#64 ++ 0xfe00fc01ff83fe37#64 ++ 0xeff803f007fe0ff8#64 : BitVec 256),
   (0xddfd0001df780000#64 ++ 0x2377f400077de000#64 ++ 0xffff0001fffc002f#64 ++ 0xabfffc0007fff000#64 : BitVec 256),
   (0xffb6ff6c00000000#64 ++ 0x13fedbfdb0000000#64 ++ 0xfffffffe0000001f#64 ++ 0xf3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [6, 9]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [12, 7]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00000000aa82d420 0x0000000002aa0b50 0x00000001ff83fe20 0x0c00000007fe0ff8

def z1 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f707e13fcf9fe 0x9c18fdc1f84ff3e7

def z2 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d89f8f1c631ffd 0xf467627e3c718c7f

def z3 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0e3f1e07fe1fb 0xdf87838fc781ff87

def z4 : W := mkw 0xb60bf836bbaefce9 0x06d82fe0daeebbf3 0xfe3ffc7fffffffff 0xfff8fff1ffffffff

def z5 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff0001fffc002f 0xabfffc0007fff000

def z6 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z7 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe00fc01ff83fe37 0xeff803f007fe0ff8

def z8 : W := mkw 0xddf40001ce500000 0x2377d00007394000 0xf9c00001ec000001 0x23e7000007b00000

def z9 : W := mkw 0xdfff3037dffc78c9 0x277ffcc0df7ff1e3 0xffff707ffffcf9ff 0xbffffdc1fffff3e7

def z10 : W := mkw 0x0000000000000000 0x0000000000000000 0x18009c011c031e35 0xe460027004700c78

def z11 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x1e3ffc7f1fffffff 0xfc78fff1fc7fffff

def z12 : W := mkw 0x0208300210a05840 0x000820c008428161 0x0618700e13e0f9fe 0x9c1861c0384f83e7

def z13 : W := mkw 0x49fd000155780000 0x2127f4000555e000 0xe1ff0001e07c002b 0x8b87fc000781f000

def z14 : W := mkw 0x4160000140500000 0x0105800005014000 0xe1e00001e07c002b 0x8b8780000781f000

def z15 : W := mkw 0x0890050800000000 0x0022401420000000 0x01d8038e00000008 0x1007600e38000000

def z16 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x01ff03fe00000008 0x1007fc0ff8000000

def z17 : W := mkw 0x0203302401885001 0x04080cc090062140 0x0607000003800000 0x00181c00000e0000

def z18 : W := mkw 0xffb7ff7c018c7089 0x17fedffdf00631c2 0xfffffffe039ce01f 0xfbfffffff80e7380

def z19 : W := mkw 0x0898050a14200a42 0x0022601428508029 0x18181c0e1c001e04 0x2060607038700078

def z20 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xe6270000e39c0002 0x0b989c00038e7000

def z21 : W := mkw 0xf720fa50ea96f4ac 0x0bdc83e943aa5bd2 0xfe20fc71ff9ffe37 0xeff883f1c7fe7ff8

def z22 : W := mkw 0xd5240000ca100000 0x2354900003284000 0xe0000000e0000000 0x0380000003800000

def z23 : W := mkw 0x9400000000000000 0x0250000000000000 0xfe00000000000007 0xa3f8000000000000

def z24 : W := mkw 0x000b0036112c28c9 0x04002c00d844b0a3 0x003f007e007c01c8 0x1000fc01f801f007

def z25 : W := mkw 0x020b302611a85841 0x04082cc09846a161 0x061f100e13e019fc 0x94187c40384f8067

def z26 : W := mkw 0x00010000cb180000 0x20000400032c6000 0x00000000e39c0000 0x08000000038e7000

def z27 : W := mkw 0xddf50001cf580000 0x2377d400073d6000 0xffe70001ef9c0003 0x2bff9c0007be7000

def z28 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xf9e0fff1fc7fffff 0xffe783ffc7f1ffff

def z29 : W := mkw 0xddb50000cb180000 0x2376d400032c6000 0xffff0000e39c000f 0xabfffc00038e7000

def z30 : W := mkw 0x9c9d00009f280000 0x22727400027ca000 0x1e1f00001f800004 0x20787c00007e0000

def z31 : W := mkw 0x00490001df780000 0x20012400077de000 0x00000001fffc0020 0x0800000007fff000

def z32 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xffffffffff83fe3f 0xfffffffffffe0ff8

def z33 : W := mkw 0x4bbf377e11ac78c9 0x152efcddf846b1e3 0x07ff73fe13fcf9fe 0x9c1ffdcff84ff3e7

def z34 : W := mkw 0xb600f8008a000000 0x02d803e002280000 0xfe00fc01ff800037 0xebf803f007fe0000

def z35 : W := mkw 0x0adb303715ec78c9 0x042b6cc0dc57b1e3 0x1fff707f1ffcf9ff 0xbc7ffdc1fc7ff3e7

def z36 : W := mkw 0x940000008a000000 0x0250000002280000 0x1e0000001f800004 0x20780000007e0000

def z37 : W := mkw 0x9c94000000000000 0x0272500000000000 0x1e1f000000000004 0x20787c0000000000

def z38 : W := mkw 0x2202ff6c00000000 0x10880bfdb0000000 0x0000fffe00000010 0x500003fff8000000

def z39 : W := mkw 0xb400c800aa028420 0x02d0032002a80a10 0xf8008c01ec030601 0x63e0023007b00c18

def z40 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff9f8fffff1fff 0xfffffe7e3ffffc7f

def z41 : W := mkw 0x00400001ce500000 0x2001000007394000 0x00000001ec000000 0x0000000007b00000

def z42 : W := mkw 0x0202302400000000 0x000808c090000000 0x063f707e0000001e 0x9018fdc1f8000000

def z43 : W := mkw 0x0008000214200a42 0x0000200008508029 0x000000001c001e00 0x0000000000700078

def z44 : W := mkw 0xfffdf801fffad420 0x23fff7e007ffeb50 0xffff6001fffce02f 0xabfffd8007fff380

def z45 : W := mkw 0x0000008200010b52 0x000000020800042d 0x0000000000031fc0 0x0400000000000c7f

def z46 : W := mkw 0x2202ffee00010b52 0x10880bffb800042d 0x0000fffe00031fd0 0x540003fff8000c7f

def z47 : W := mkw 0x0048008314610b52 0x000120020c51842d 0x000000011c631fe0 0x0400000004718c7f

def z48 : W := mkw 0x000b003611ac78c9 0x04002c00d846b1e3 0x003f007e13fcf9e8 0x1c00fc01f84ff3e7

def z49 : W := mkw 0x9e9f3d2c9f280000 0x327a7cf4b27ca000 0x1e1f1c0e1f800004 0x20787c70387e0000

def z50 : W := mkw 0x0000008000010110 0x0000000200000404 0x00008380000301d0 0x5400020e00000c07

def z51 : W := mkw 0x0009000011280000 0x000024000044a000 0x063f000013fc002e 0x8818fc00004ff000

def z52 : W := mkw 0xf760fad1ead7f5bc 0x0bdd83eb47ab5fd6 0xffe0fff1ffffffff 0xffff83ffc7ffffff

def z53 : W := mkw 0x0000058a00010b52 0x000000162800042d 0x18009f8f1c031ff5 0xf460027e3c700c7f

def z54 : W := mkw 0x2000c2d02007a19c 0x0880030b40801e86 0xe000e3f1e003e1f3 0xdf80038fc7800f87

def z55 : W := mkw 0x02033034018c7089 0x04080cc0d00631c2 0x06276070039ce002 0x08189d81c00e7380

def z56 : W := mkw 0x2000c2d02007a19c 0x0880030b40801e86 0x0020e3f0007fe1fa 0xdc00838fc001ff87

def z57 : W := mkw 0x436b32f751fd79dd 0x0d0daccbdd47f5e7 0x07ff73fe13fcf9fe 0x9c1ffdcff84ff3e7

def z58 : W := mkw 0xffffff6dfffad420 0x33fffffdb7ffeb50 0xfffffffffffffe3f 0xfffffffffffffff8

def z59 : W := mkw 0x0890050800000000 0x0022401420000000 0x19c08f8000000001 0x6067023e00000000

def z60 : W := mkw 0x0009000211a85841 0x040024000846a161 0x0000000013801800 0x00000000004e0060

def z61 : W := mkw 0x0200300000805000 0x000800c000020140 0x060070001380f836 0x8c1801c0004e03e0

def z62 : W := mkw 0x9e9d38009fa85420 0x227a74e0027ea150 0x1e1f1c001f801e04 0x20787c70007e0078

def z63 : W := mkw 0x00090012112c28c9 0x040024004844b0a3 0x00000000007c01c0 0x000000000001f007

def z64 : W := mkw 0x0209301211ac78c9 0x040824c04846b1e3 0x0600700013fcf9f6 0x8c1801c0004ff3e7

def z65 : W := mkw 0xddff076ddf780000 0x3377fc1db77de000 0xffff03fffffc002f 0xbbfffc0ffffff000

def z66 : W := mkw 0x636bf2f771fff9dd 0x0d8dafcbddc7ffe7 0xe7fff3fff3fff9ff 0xdf9fffcfffcfffe7

def z67 : W := mkw 0x4160000140500000 0x0105800005014000 0xe1c00001e0000001 0x0387000007800000

def z68 : W := mkw 0x6120c2506016a08c 0x0984830941805a82 0xe0206070e01ce002 0x0b808181c3807380

def z69 : W := mkw 0x69f8c7db7477abde 0x09a7e31f6dd1deaf 0xf9f8fffffc7fffff 0xffe7e3fffff1ffff

def z70 : W := mkw 0xbed8fd8bbee3df72 0x02fb63f62efb8f7d 0xffd8ff8fffe3ffff 0xffff63fe3fff8fff

def z71 : W := mkw 0x2200f8002082d420 0x008803e000820b50 0x0000fc000003fe10 0x440003f000000ff8

def z72 : W := mkw 0x940000008a000000 0x0250000002280000 0xfe000001ff800027 0xabf8000007fe0000

def z73 : W := mkw 0x940008008a000420 0x0250002002280010 0x18000c000c000600 0x2060003000300018

def z74 : W := mkw 0x02003000aa82d420 0x000800c002aa0b50 0x06007001ff83fe36 0x8c1801c007fe0ff8

def z75 : W := mkw 0x69f8c7db7477abde 0x09a7e31f6dd1deaf 0xe1f8e3ffe07fe1fb 0xdf87e38fff81ff87

def z76 : W := mkw 0x49fd000155780000 0x2127f4000555e000 0x01ff0000007c0008 0x0007fc000001f000

def z77 : W := mkw 0x0adb35bf15ed7bdb 0x042b6cd6fc57b5ef 0x1fffffff1fffffff 0xfc7ffffffc7fffff

def z78 : W := mkw 0x632bf27671bef8cd 0x0d8cafc9d9c6fbe3 0xe63f707ef3fcf9fe 0x9f98fdc1fbcff3e7

def z79 : W := mkw 0x00090010112c2088 0x000024004044b082 0x063f607013fce1fe 0x9c18fd81c04ff387

def z80 : W := mkw 0x69f8c7cb14610b52 0x01a7e31f2c51842d 0xf9f8ffff1c631fff 0xf7e7e3fffc718c7f

def z81 : W := mkw 0xfdb4cf48aa028420 0x13f6d33d22a80a10 0xf9c08f81ec030601 0x63e7023e07b00c18

def z82 : W := mkw 0x6168c2d37077a9dc 0x0985a30b4dc1dea7 0xe1f8f3fff07ff9ff 0xdf87e3cfffc1ffe7

def z83 : W := mkw 0x2000cf4800000000 0x1080033d20000000 0x00008f8000000000 0x4000023e00000000

def z84 : W := mkw 0x08d9059b15ed7bdb 0x042364166c57b5ef 0x19d89f8f1ffffffd 0xfc67627e3c7fffff

def z85 : W := mkw 0x0898000014200000 0x0022600000508000 0x181800001c000004 0x2060600000700000

def z86 : W := mkw 0x0adb35bf15ed7bdb 0x042b6cd6fc57b5ef 0x07ff73fe13fcf9fe 0x9c1ffdcff84ff3e7

def z87 : W := mkw 0x6120c24060128004 0x0984830901804a00 0xe0000000e0000000 0x0380000003800000

def z88 : W := mkw 0x0ad8358b14e15b52 0x002b60d62c53856d 0x1fd8ff8f1fe3ffff 0xfc7f63fe3c7f8fff

def z89 : W := mkw 0x2202f8362086fce9 0x04880be0d8821bf3 0x0000fc7e0003ffd0 0x540003f1f8000fff

def z90 : W := mkw 0xfdb4cf4800000000 0x13f6d33d20000000 0xf9c08f8000000001 0x63e7023e00000000

def z91 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0x1fff00001ffc000c 0x207ffc00007ff000

def z92 : W := mkw 0x0890050800000000 0x0022401420000000 0x19d89f8f1c031e3d 0xf467627e3c700c78

def z93 : W := mkw 0x0202302400000000 0x000808c090000000 0x0627607000000002 0x00189d81c0000000

def z94 : W := mkw 0x020b302611a85841 0x04082cc09846a161 0x061f100e13801804 0x00187c40384e0060

def z95 : W := mkw 0x6160c2c160538114 0x0985830b05814e04 0xe1c08381e0030001 0x4387020e07800c00

def z96 : W := mkw 0x08d0058b04410b52 0x002340162c11042d 0x19c09f8f0c031fd1 0x7467027e3c300c7f

def z97 : W := mkw 0xfff6ff6d40500000 0x13ffdbfdb5014000 0xffffffffe07c003f 0xfbffffffff81f000

def z98 : W := mkw 0x0209300011a85000 0x000824c00046a140 0x063f700013fcf83e 0x8c18fdc0004ff3e0

def z99 : W := mkw 0x004000916057a19c 0x0801000245815e86 0x00000001e07fe1e0 0x0c0000000781ff87

def z100 : W := mkw 0x2202fa6400000000 0x10880be990000000 0x0000607000000000 0x00000181c0000000

def z101 : W := mkw 0x020a302610200840 0x000828c098408021 0x063f707e106019fe 0x9418fdc1f8418067

def z102 : W := mkw 0x49f807db54752bde 0x0927e01f6d51d4af 0x19f89fff1c7f1ffd 0xf467e27ffc71fc7f

def z103 : W := mkw 0xffb6ff6c2082d420 0x13fedbfdb0820b50 0xfffffffe0003fe1f 0xf7fffffff8000ff8

def z104 : W := mkw 0x0048008314610b52 0x000120020c51842d 0x01c083811c631ff9 0xd407020e04718c7f

def z105 : W := mkw 0xddbd0000df380000 0x2376f400037ce000 0xfe3f0000ff9c0006 0x2bf8fc0003fe7000

def z106 : W := mkw 0xfffdfad1fffff5bc 0x2bfff7eb47ffffd6 0xfffffff1ffffffff 0xffffffffc7ffffff

def z107 : W := mkw 0xbe96fd2c00000000 0x12fa5bf4b0000000 0xfe1ffc0e00000017 0xe3f87ff038000000

def z108 : W := mkw 0x69b6c76c00000000 0x11a6db1db0000000 0xe1ffe3fe0000001b 0xd387ff8ff8000000

def z109 : W := mkw 0x960038008a805420 0x025800e0022a0150 0x1e001c001f801e04 0x20780070007e0078

def z110 : W := mkw 0x024b30b711ed79d9 0x04092cc2dc47b5e7 0x07fff3ff13fff9ff 0xdc1fffcffc4fffe7

def z111 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xe7ff0000e3fc000a 0x0b9ffc00038ff000

def z112 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xe6006000e380e002 0x0b980180038e0380

def z113 : W := mkw 0x00000000aa82d420 0x0000000002aa0b50 0x18009c01ff83fe35 0xec60027007fe0ff8

def z114 : W := mkw 0x2000c2d02007a19c 0x0880030b40801e86 0x0000e3f00003e1d0 0x5400038fc0000f87

def z115 : W := mkw 0xffffff6ddf780000 0x33fffffdb77de000 0xfffffffffffc003f 0xfbfffffffffff000

def z116 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffffffff1c031e3f 0xf7fffffffc700c78

def z117 : W := mkw 0x6160c7db6057abde 0x0985831f6d815eaf 0xe1e0ffffe07ffffb 0xdf8783ffff81ffff

def z118 : W := mkw 0x0890050800000000 0x0022401420000000 0x19d89f8e0000001d 0xf067627e38000000

def z119 : W := mkw 0xd56d0001df780000 0x2355b400077de000 0xe6270001fffc0022 0x0b989c0007fff000

def z120 : W := mkw 0xfdf4c2c1ee538114 0x2bf7d30b07b94e04 0xf9c08381ec030001 0x63e7020e07b00c00

def z121 : W := mkw 0x0202302400805000 0x000808c090020140 0x063f707e1380f83e 0x9c18fdc1f84e03e0

def z122 : W := mkw 0xddf40001ce500000 0x2377d00007394000 0xffc00001ff800027 0xabff000007fe0000

def z123 : W := mkw 0x2200fd8a2083df72 0x008803f628820f7d 0x0000ff8e0003ffd0 0x540003fe38000fff

def z124 : W := mkw 0x9e963d2c00000000 0x127a58f4b0000000 0x1e1f1c0e00000004 0x20787c7038000000

def z125 : W := mkw 0xb600f810aa86f4a8 0x02d803e042aa1bd2 0xfe20fc71ffffffff 0xfff883f1c7ffffff

def z126 : W := mkw 0x02023036008478c9 0x040808c0d80211e3 0x0000707e0000f9d0 0x140001c1f80003e7

def z127 : W := mkw 0xfff6fffd6057a19c 0x1bffdbfff5815e86 0xffffffffe07fe1ff 0xffffffffff81ff87

def z128 : W := mkw 0x08d90001df780000 0x20236400077de000 0x19d80001fffc002d 0xa867600007fff000

def z129 : W := mkw 0x6120c24000000000 0x0184830900000000 0xe1e0e3f00000001b 0xd387838fc0000000

def z130 : W := mkw 0xffb6ff6c8a000000 0x13fedbfdb2280000 0xffffffffff80003f 0xfbfffffffffe0000

def z131 : W := mkw 0x49f807db54752bde 0x0927e01f6d51d4af 0x01f803fe007c01c8 0x1007e00ff801f007

def z132 : W := mkw 0xf726fa6400000000 0x13dc9be990000000 0xe627607000000002 0x03989d81c0000000

def z133 : W := mkw 0xffb7ff6ccb180000 0x33fedffdb32c6000 0xfffffffee39c001f 0xfbfffffffb8e7000

def z134 : W := mkw 0xbe96ff6c00000000 0x12fa5bfdb0000000 0x1e1ffffe00000014 0x70787ffff8000000

def z135 : W := mkw 0x0000050a00000a42 0x0000001428000029 0x00001c0e00001e00 0x0000007038000078

def z136 : W := mkw 0x2a92ff6c00000000 0x10aa4bfdb0000000 0x19d8fffe0000001d 0xf06763fff8000000

def z137 : W := mkw 0x000002d00005219c 0x0800000b40001486 0x000003f0000001c0 0x1000000fc0000007

def z138 : W := mkw 0xfffdf801fffad420 0x23fff7e007ffeb50 0xfffffc01fffffe3f 0xeffffff007fffff8

def z139 : W := mkw 0xffbfff6c11280000 0x13fefffdb044a000 0xfffffffe13fc003f 0xfbfffffff84ff000

def z140 : W := mkw 0x6362f2f760d7f9dd 0x0d8d8bcbdd835fe7 0xe1e0f3ffe07ff9fb 0xdf8783cfff81ffe7

def z141 : W := mkw 0x4120000040100000 0x0104800001004000 0xe0200000e01c0002 0x0b80800003807000

def z142 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x19ff9ffe0000001d 0xf067fe7ff8000000

def z143 : W := mkw 0x0000050800000000 0x0000001420000000 0x00009f8e00000010 0x5000027e38000000

def z144 : W := mkw 0x2040c2d12047a19c 0x0881030b44811e86 0x01c0e3f10063e1f9 0xd407038fc4018f87

def z145 : W := mkw 0x0001000001080000 0x0000040000042000 0x06270000039c0002 0x08189c00000e7000

def z146 : W := mkw 0x00480083bee3df72 0x000120020efb8f7d 0x00000001ffe3ffe0 0x0c00000007ff8fff

def z147 : W := mkw 0xf726fa6400000000 0x13dc9be990000000 0xfe27fc7000000017 0xe3f89ff1c0000000

def z148 : W := mkw 0xd7273034cb9c7089 0x275c9cc0d32e71c2 0xe6276070e39ce002 0x0b989d81c38e7380

def z149 : W := mkw 0xffbeff6e14200a42 0x13fefbfdb8508029 0xfffffffe1c001e1f 0xf3fffffff8700078

def z150 : W := mkw 0x2040c08120438110 0x0081030204810e04 0xe1c0e381e063e1fb 0xdf87038e07818f87

def z151 : W := mkw 0x0009000211280840 0x000024000844a021 0x063f100e13fc19fe 0x9c18fc40384ff067

def z152 : W := mkw 0xffb6ff6c00805000 0x13fedbfdb0020140 0xfffffffe1380f83f 0xfffffffff84e03e0

def z153 : W := mkw 0x0202302400000000 0x000808c090000000 0x0000707e00000010 0x100001c1f8000000

def z154 : W := mkw 0x2202ff6c00000000 0x10880bfdb0000000 0x063ffffe0000001e 0xd018fffff8000000

def z155 : W := mkw 0xdfff3025df780000 0x237ffcc0977de000 0xffff707ffffc003f 0xbbfffdc1fffff000

def z156 : W := mkw 0x02033034018c7089 0x04080cc0d00631c2 0x06277070139cf836 0x8c189dc1c04e73e0

def z157 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xfffffffee380e01f 0xfbfffffffb8e0380

def z158 : W := mkw 0x49fd0001df780000 0x2127f400077de000 0x01ff0001fffc0028 0x0807fc0007fff000

def z159 : W := mkw 0xffbfff7ebbaefce9 0x17fefffdfaeebbf3 0xffffffffffffffff 0xffffffffffffffff

def z160 : W := mkw 0x94490001df780000 0x22512400077de000 0xfe000001fffc0027 0xabf8000007fff000

def z161 : W := mkw 0x0890050804000202 0x0022401420100008 0x18000c000c000600 0x2060003000300018

def z162 : W := mkw 0xfffeffef14610b52 0x13fffbffbc51842d 0xffffffff1c631fff 0xf7fffffffc718c7f

def z163 : W := mkw 0x4120024000000000 0x0104800900000000 0x01e003f000000008 0x1007800fc0000000

def z164 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x01d8038f1c631fe8 0x1407600e3c718c7f

def z165 : W := mkw 0xb609f812bbaefce9 0x06d827e04aeebbf3 0xfe00fc01fffffff7 0xeff803f007ffffff

def z166 : W := mkw 0x2200f8002082d420 0x008803e000820b50 0x000060000000e000 0x0000018000000380

def z167 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x01d89f8e00631fd8 0x5407627e38018c7f

def z168 : W := mkw 0xb600f80000000000 0x02d803e000000000 0xfe00fc0000000017 0xe3f803f000000000

def z169 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe00ec01ef83e603 0x6bf803b007be0f98

def z170 : W := mkw 0x4169000151780000 0x0105a4000545e000 0xe7ff0001f3fc002f 0x8b9ffc0007cff000

def z171 : W := mkw 0x2202f2f62087f9dd 0x0c880bcbd8821fe7 0x0000f3fe0003f9d0 0x540003cff8000fe7

def z172 : W := mkw 0xffffffefdf790b52 0x33ffffffbf7de42d 0xffffffffffff1fff 0xfffffffffffffc7f

def z173 : W := mkw 0x2202fffc2007a19c 0x18880bfff0801e86 0x0000fffe0003e1d0 0x540003fff8000f87

def z174 : W := mkw 0x0000001000042088 0x0000000040001082 0x00206070007ce1fa 0x9c008181c001f387

def z175 : W := mkw 0xfdb4cf4800000000 0x13f6d33d20000000 0xf9e0eff00000001b 0xf3e783bfc0000000

def z176 : W := mkw 0xdffd3001dff85000 0x237ff4c0077fe140 0xffff7001fffcf83f 0xaffffdc007fff3e0

def z177 : W := mkw 0x0040008100410110 0x0001000204010404 0x01c08381006301f9 0xd407020e04018c07

def z178 : W := mkw 0xddfd0081df790110 0x2377f402077de404 0xffff8381ffff01ff 0xfffffe0e07fffc07

def z179 : W := mkw 0x6120c24020028000 0x0184830900800a00 0xe1e0e3f1e003e03b 0xdf87838fc7800f80

def z180 : W := mkw 0xb600f80000805000 0x02d803e000020140 0xfe00fc001380f837 0xeff803f0004e03e0

def z181 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f107e13fc19cc 0x1018fc41f84ff067

def z182 : W := mkw 0xf72ffa7611ac78c9 0x17dcbfe9d846b1e3 0xe63f707e13fcf9fe 0x9f98fdc1f84ff3e7

def z183 : W := mkw 0x020b302611a85841 0x04082cc09846a161 0x063f707e1380181e 0x9018fdc1f84e0060

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z185 : W := mkw 0x6120c2d02007a19c 0x0984830b40801e86 0xe1e0e3f00003e1db 0xd787838fc0000f87

def z186 : W := mkw 0x0008000210200840 0x0000200008408021 0x0018100e106019fc 0x9400604038418067

def z187 : W := mkw 0x416002d14055219c 0x0905800b45015486 0x01e003f0007c01c8 0x1007800fc001f007

def z188 : W := mkw 0x632bf27611ac78c9 0x058cafc9d846b1e3 0xe7fff3fe13fcf9ff 0xdf9fffcff84ff3e7

def z189 : W := mkw 0xddff0037df7c28c9 0x2777fc00df7df0a3 0xffff007ffffc01ef 0xbbfffc01fffff007

def z190 : W := mkw 0xb602f824aa82d420 0x02d80be092aa0b50 0xfe3ffc7fff83fe3f 0xfff8fff1fffe0ff8

def z191 : W := mkw 0xfffeff6d14600000 0x13fffbfdb4518000 0xffffffff1c60003f 0xf3fffffffc718000

def z192 : W := mkw 0x0040058b00410b52 0x000100162c01042d 0x01c09f8f00631ff9 0xd407027e3c018c7f

def z193 : W := mkw 0xddb4000000000000 0x0376d00000000000 0xffff00000000000f 0xa3fffc0000000000

def z194 : W := mkw 0x9c9d00009f280000 0x22727400027ca000 0x1e3f00001ffc002e 0xa878fc00007ff000

def z195 : W := mkw 0x08d8000114600000 0x0023600004518000 0x19d800011c60002d 0xa067600004718000

def z196 : W := mkw 0x0048008314610b52 0x000120020c51842d 0x18009c011c631ff5 0xe460027004718c7f

def z197 : W := mkw 0x024b30b715ed7bdb 0x04092cc2dc57b5ef 0x063f707f1ffffffe 0x9c18fdc1fc7fffff

def z198 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x18181c0f1c631fe4 0x246060703c718c7f

def z199 : W := mkw 0x020235be00857bdb 0x040808d6f80215ef 0x0000fffe0003ffd0 0x540003fff8000fff

def z200 : W := mkw 0xddfd0013dffc78c9 0x2777f4004f7ff1e3 0xffff0001fffcf9ef 0xaffffc0007fff3e7

def z201 : W := mkw 0xfffeffefbee3df72 0x13fffbffbefb8f7d 0xffffffffffe3ffff 0xffffffffffff8fff

def z202 : W := mkw 0xfdfdc2d1ff7fa19c 0x2bf7f70b47fdfe86 0xffffe3f1ffffe1ff 0xffffff8fc7ffff87

def z203 : W := mkw 0xffb6ff7e008478c9 0x17fedbfdf80211e3 0xfffffffe0000f9df 0xf7fffffff80003e7

def z204 : W := mkw 0xddfc000114600000 0x0377f00004518000 0xffff00011c60002f 0xa3fffc0004718000

def z205 : W := mkw 0x94000000aa82d420 0x0250000002aa0b50 0xfe000001ff83fe27 0xaff8000007fe0ff8

def z206 : W := mkw 0x0000058a00010b52 0x000000162800042d 0x00009f8e00031fd0 0x5400027e38000c7f

def z207 : W := mkw 0x9e983d0a9ea05e62 0x027a60f42a7a8179 0x1e181c0e1f801e04 0x20786070387e0078

def z208 : W := mkw 0x0040000140500000 0x0001000005014000 0x00000001e07c0020 0x080000000781f000

def z209 : W := mkw 0xb400c800aa028420 0x02d0032002a80a10 0xf800ec01ec03e633 0xefe003b007b00f98

def z210 : W := mkw 0xdfb63f6c00000000 0x137ed8fdb0000000 0x1fff1ffe0000000c 0x307ffc7ff8000000

def z211 : W := mkw 0xb608f802baa2dc60 0x02d823e00aea8b71 0xfe18fc0fffe3ffff 0xfff863f03fff8fff

def z212 : W := mkw 0x08d0058904410312 0x002340162411040c 0x19c08f810c030601 0x6067023e04300c18

def z213 : W := mkw 0xddfd050bdf780a42 0x2377f4142f7de029 0xffff1c0ffffc1e2f 0xabfffc703ffff078

def z214 : W := mkw 0x2000c00020028000 0x0080030000800a00 0xe000e001e003e033 0xcf80038007800f80

def z215 : W := mkw 0x49fe07ef14610b52 0x1127f81fbc51842d 0x19ff9fff1c631ffd 0xf467fe7ffc718c7f

def z216 : W := mkw 0x616bc2f7717fa9dd 0x0d85af0bddc5fea7 0xe1ffe3ffe07fe1fb 0xdf87ff8fff81ff87

def z217 : W := mkw 0x0000058a00010b52 0x000000162800042d 0x0000038e000001c0 0x1000000e38000007

def z218 : W := mkw 0x0049009371fff9dd 0x0c0124024dc7ffe7 0x00000001f3fff9e0 0x0c00000007cfffe7

def z219 : W := mkw 0x416002c140510114 0x0905800b05014404 0x01c0038000000000 0x0007000e00000000

def z220 : W := mkw 0xfdfdc801ff7a8420 0x23f7f72007fdea10 0xffff8c01ffff062f 0xebfffe3007fffc18

def z221 : W := mkw 0xb400c800aa82d420 0x02d0032002aa0b50 0xf8008c01ff83fe21 0x6fe0023007fe0ff8

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c0838000000019 0xd007020e00000000

def z223 : W := mkw 0xddb400008a000000 0x0376d00002280000 0xffff0001ff80002f 0xabfffc0007fe0000

def z224 : W := mkw 0xd5600001ca500000 0x0355800007294000 0xffe00001fffc002f 0xabff800007fff000

def z225 : W := mkw 0x9c9d00009f280000 0x22727400027ca000 0xfe1f0001ff800027 0xabf87c0007fe0000

def z226 : W := mkw 0x6362f2f56057a19c 0x098d8bcbd5815e86 0xe7fff3ffe07fe1ff 0xdf9fffcfff81ff87

def z227 : W := mkw 0x6120c24000000000 0x0184830900000000 0xe020607000000002 0x03808181c0000000

def z228 : W := mkw 0x49b4000000000000 0x0126d00000000000 0x01ff000000000008 0x0007fc0000000000

def z229 : W := mkw 0x0009001211ac78c9 0x040024004846b1e3 0x0000000013fcf9e0 0x0c000000004ff3e7

def z230 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f607e03fce1ca 0x1818fd81f80ff387

def z231 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xfe270001ff9c0027 0xabf89c0007fe7000

def z232 : W := mkw 0x49fd058b55790b52 0x2127f4162d55e42d 0x19ff9f8f1c7f1ffd 0xf467fe7e3c71fc7f

def z233 : W := mkw 0x020b3036bbaefce9 0x04082cc0daeebbf3 0x063f707ffffffffe 0x9c18fdc1ffffffff

def z234 : W := mkw 0x69f6c7fd6057a19c 0x19a7db1ff5815e86 0xe1ffe3ffe07fe1fb 0xdf87ff8fff81ff87

def z235 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x01d8038e006001c8 0x1007600e38018007

def z236 : W := mkw 0xddfc0001de700000 0x2377f0000779c000 0xf9d80001fc60002d 0xa3e7600007f18000

def z237 : W := mkw 0x0009000011280000 0x000024000044a000 0x003f0000007c0008 0x0000fc000001f000

def z238 : W := mkw 0x69f0c7d96057a19c 0x09a7c31f65815e86 0xf9f8ffffe07fe1ff 0xffe7e3ffff81ff87

def z239 : W := mkw 0xfdfccfcb14610b52 0x13f7f33f2c51842d 0xf9d89f8f1c631ffd 0xf7e7627e3c718c7f

def z240 : W := mkw 0xdfbf303611ac78c9 0x077efcc0d846b1e3 0xffff707e13fcf9ff 0xbffffdc1f84ff3e7

def z241 : W := mkw 0xfff4f801eed2d420 0x23ffd3e007bb4b50 0xffc0fc01ff83fe37 0xefff03f007fe0ff8

def z242 : W := mkw 0x6160c2d1ead7f5bc 0x0985830b47ab5fd6 0xe1e0e3f1fffffffb 0xdf87838fc7ffffff

def z243 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d89f8f1c031e05 0x6067627e3c700c78

def z244 : W := mkw 0x0009000011280000 0x000024000044a000 0x0000000013fc0020 0x08000000004ff000

def z245 : W := mkw 0x0008058a10210b52 0x000020162840842d 0x00189f8e10631ffc 0xd400627e38418c7f

def z246 : W := mkw 0xffbfff7e11ac78c9 0x17fefffdf846b1e3 0xfffffffe13fcf9ff 0xfffffffff84ff3e7

def z247 : W := mkw 0xf726fa746016a08c 0x1bdc9be9d1805a82 0xe6276070e01ce002 0x0b989d81c3807380

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000100010001834 0x8400004000400060

def z249 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1c0e3f1e003e1d1 0x5787038fc7800f87

def z250 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfe3f7c7e00000006 0x23f8fdf1f8000000

def z251 : W := mkw 0xb600fd8aaa83df72 0x02d803f62aaa0f7d 0xfe00ff8fff83fff7 0xfff803fe3ffe0fff

def z252 : W := mkw 0xf726fa64aa82d420 0x13dc9be992aa0b50 0xfe27fc71ff83fe37 0xeff89ff1c7fe0ff8

def z253 : W := mkw 0x6322f26400000000 0x018c8bc990000000 0xe7fff3fe0000001f 0xd39fffcff8000000

def z254 : W := mkw 0x960038008a805420 0x025800e0022a0150 0x0600000003800000 0x00180000000e0000

def z255 : W := mkw 0x00000000aa82d420 0x0000000002aa0b50 0x00000000e380e000 0x08000000038e0380

def z256 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0x01e0e3f0007fe1d8 0x5407838fc001ff87

def z257 : W := mkw 0x0040008100410110 0x0001000204010404 0x00000001006301e0 0x0400000004018c07

def z258 : W := mkw 0x0048000114600000 0x0001200004518000 0x000000011c600020 0x0000000004718000

def z259 : W := mkw 0x4125000041180000 0x2104940001046000 0x00270000001c0000 0x00009c0000007000

def z260 : W := mkw 0x2000c000aa82d420 0x0080030002aa0b50 0xe000e001ff83fe33 0xcf80038007fe0ff8

def z261 : W := mkw 0x00490001fffad420 0x2001240007ffeb50 0x00000001fffffe20 0x0c00000007fffff8

def z262 : W := mkw 0x2200f0002082d000 0x008803c000820b40 0xe600f001f383f837 0xcf9803c007ce0fe0

def z263 : W := mkw 0xf727fa74018c7089 0x17dc9fe9d00631c2 0xe6276070039ce002 0x0b989d81c00e7380

def z264 : W := mkw 0x49fd000155780000 0x2127f4000555e000 0x19ff00011c7c002d 0xa067fc000471f000

def z265 : W := mkw 0x08d8059b14652bda 0x002360166c5194af 0x19f8ffff1c7fffff 0xfc67e3fffc71ffff

def z266 : W := mkw 0xdfb6302400000000 0x037ed8c090000000 0xffff707e0000001f 0xb3fffdc1f8000000

def z267 : W := mkw 0xffb6ffee00010b52 0x13fedbffb800042d 0xfffffffe00031fdf 0xf7fffffff8000c7f

def z268 : W := mkw 0x0a9b353e11ac78c9 0x042a6cd4f846b1e3 0x1ffffffe13fcf9ff 0xfc7ffffff84ff3e7

def z269 : W := mkw 0xfffffffdff7fa19c 0x3bfffffff7fdfe86 0xffffffffffffe1ff 0xffffffffffffff87

def z270 : W := mkw 0xbe96fd2caa82d420 0x12fa5bf4b2aa0b50 0xfe1ffc0fff83fe37 0xeff87ff03ffe0ff8

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x18008c010c030601 0x6060023004300c18

def z272 : W := mkw 0xdfff35bfdffd7bdb 0x277ffcd6ff7ff5ef 0xffffffffffffffff 0xffffffffffffffff

def z273 : W := mkw 0x0200300000805000 0x000800c000020140 0x060060000380e002 0x08180180000e0380

def z274 : W := mkw 0x0008000210200840 0x0000200008408021 0x18189c0f1c631ffd 0xf46062703c718c7f

def z275 : W := mkw 0xffb6ff6c20028000 0x13fedbfdb0800a00 0xffffffffe003e03f 0xffffffffff800f80

def z276 : W := mkw 0x08d9000115680000 0x002364000455a000 0x1fff00011ffc002f 0xa87ffc00047ff000

def z277 : W := mkw 0x69f0c7d96457a39e 0x09a7c31f65915e8e 0xf9e0eff1ec7fe7fb 0xffe783bfc7b1ff9f

def z278 : W := mkw 0xbed8f801bee2d420 0x02fb63e006fb8b50 0xffd8fc01ffe3fe3f 0xefff63f007ff8ff8

def z279 : W := mkw 0x004000914055219c 0x0801000245015486 0x00000000007c01c0 0x000000000001f007

def z280 : W := mkw 0xf524ca4000000000 0x13d4932900000000 0xe000000000000000 0x0380000000000000

def z281 : W := mkw 0x4bff303755fc78c9 0x252ffcc0dd57f1e3 0x07ff707e13fcf9fe 0x9c1ffdc1f84ff3e7

def z282 : W := mkw 0xddf40001ce500000 0x2377d00007394000 0xf9e00001ec7c002b 0xabe7800007b1f000

def z283 : W := mkw 0xffbeff6e10200840 0x13fefbfdb8408021 0xfffffffe106019ff 0xf7fffffff8418067

def z284 : W := mkw 0x08db05bf156d2bdb 0x04236c16fc55b4af 0x19ff9fff1c7f1ffd 0xf467fe7ffc71fc7f

def z285 : W := mkw 0x000b0036112c28c9 0x04002c00d844b0a3 0x003f107e107c19fc 0x9400fc41f841f067

def z286 : W := mkw 0x9e9f30369fac78c9 0x267a7cc0da7eb1e3 0x1e3f707e1ffcf9fe 0xbc78fdc1f87ff3e7

def z287 : W := mkw 0x2040c0916057a19c 0x0881030245815e86 0xe000e001e07fe1f3 0xcf8003800781ff87

def z288 : W := mkw 0x0ada35af14610b52 0x002b68d6bc51842d 0x1fffffff1c631fff 0xf47ffffffc718c7f

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000011c000025 0xa060000004700000

def z290 : W := mkw 0x9600380000000000 0x025800e000000000 0x1e001c0000000004 0x2078007000000000

def z291 : W := mkw 0x416b02f7517d29dd 0x0d05ac0bdd45f4a7 0x01ff03fe007c01c8 0x1007fc0ff801f007

def z292 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d81f8e1c601fcc 0x3067607e3871807f

def z293 : W := mkw 0xfffdfd8bfffbdf72 0x23fff7f62fffef7d 0xffffff8fffffffff 0xfffffffe3fffffff

def z294 : W := mkw 0x0049000155780000 0x200124000555e000 0x00000000007c0000 0x000000000001f000

def z295 : W := mkw 0xd52d0000db380000 0x2354b400036ce000 0xe63f0000f3fc002e 0x8b98fc0003cff000

def z296 : W := mkw 0x020a303610a478c9 0x040828c0d84291e3 0x0018707e1060f9fc 0x940061c1f84183e7

def z297 : W := mkw 0xddfd0083df790b52 0x2377f4020f7de42d 0xffff0001ffff1fef 0xaffffc0007fffc7f

def z298 : W := mkw 0x08db05bf156d2bdb 0x04236c16fc55b4af 0x01ff03fe007c01c8 0x1007fc0ff801f007

def z299 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0e3f1e01fe003 0x4b87838fc7807f80

def z300 : W := mkw 0xbed0fd89aec3d732 0x02fb43f626bb0f5c 0xffc0ff81ff83fe37 0xefff03fe07fe0ff8

def z301 : W := mkw 0xfffeffff7477abde 0x1bfffbfffdd1deaf 0xfffffffffc7fffff 0xfffffffffff1ffff

def z302 : W := mkw 0x02023036008478c9 0x040808c0d80211e3 0x063f707e0000f9de 0x9418fdc1f80003e7

def z303 : W := mkw 0x08d9058bdf790b52 0x202364162f7de42d 0x19d89f8fffff1ffd 0xfc67627e3ffffc7f

def z304 : W := mkw 0x416000916057a19c 0x0905800245815e86 0xe1e00001e07fe1eb 0x8f8780000781ff87

def z305 : W := mkw 0xffb6ff6c8a805420 0x13fedbfdb22a0150 0xfffffffe1f801e1f 0xf3fffffff87e0078

def z306 : W := mkw 0xffbfff6e11a85841 0x17fefffdb846a161 0xfffffffe1380181f 0xf3fffffff84e0060

def z307 : W := mkw 0x960b38269ba85c61 0x06582ce09a6ea171 0x1e1f1c0e1f801e04 0x20787c70387e0078

def z308 : W := mkw 0x960038008a805420 0x025800e0022a0150 0x1e009c011f831e35 0xe4780270047e0c78

def z309 : W := mkw 0xf565c2d1eb5fa19c 0x2bd5970b47ad7e86 0xe7e7e3f1e3ffe1fb 0xdf9f9f8fc78fff87

def z310 : W := mkw 0xfdf4cfc904410312 0x13f7d33f2411040c 0xf9c08f810c030601 0x63e7023e04300c18

def z311 : W := mkw 0x0009000011280000 0x000024000044a000 0x061f000013800004 0x00187c00004e0000

def z312 : W := mkw 0xfffffa65df780000 0x33ffffe9977de000 0xffff6071fffc002f 0xabfffd81c7fff000

def z313 : W := mkw 0x02023036008478c9 0x040808c0d80211e3 0x0600707e1380f9f6 0x9c1801c1f84e03e7

def z314 : W := mkw 0x08d0000104400000 0x0023400004110000 0x19c000010c000001 0x2067000004300000

def z315 : W := mkw 0x69f8c7cb74738b56 0x09a7e31f2dd1ce2d 0xf9d89f8ffc631ffd 0xf7e7627e3ff18c7f

def z316 : W := mkw 0x49fd058b55790b52 0x2127f4162d55e42d 0x01ff038e007c01c8 0x1007fc0e3801f007

def z317 : W := mkw 0x000900009f280000 0x20002400027ca000 0x000000001f800000 0x00000000007e0000

def z318 : W := mkw 0x220bf03631aef8c9 0x04882fc0d8c6bbe3 0xe63ff07ff3fff9ff 0xdf98ffc1ffcfffe7

def z319 : W := mkw 0xf720fa40aa82d420 0x03dc83e902aa0b50 0xffe0fff1ff83fe3f 0xffff83ffc7fe0ff8

def z320 : W := mkw 0x9e963d2c8a805420 0x127a58f4b22a0150 0x1e1f1c0e1f801e04 0x20787c70387e0078

def z321 : W := mkw 0x2200f80000000000 0x008803e000000000 0x0000fc0000000010 0x400003f000000000

def z322 : W := mkw 0xfffdf801df780000 0x23fff7e0077de000 0xfffffc01fffc003f 0xebfffff007fff000

def z323 : W := mkw 0x0890058a00010b52 0x002240162800042d 0x19d89f8e00031fdd 0xf467627e38000c7f

def z324 : W := mkw 0x6322ff6c00000000 0x118c8bfdb0000000 0xe1e0fffe0000001b 0xd38783fff8000000

def z325 : W := mkw 0x0049009315ed7bdb 0x040124024c57b5ef 0x000000011fffffe0 0x0c000000047fffff

def z326 : W := mkw 0xf766faf56057a19c 0x1bdd9bebd5815e86 0xe7e7e3f1e07fe1fb 0xdf9f9f8fc781ff87

def z327 : W := mkw 0xddfd0589df790312 0x2377f416277de40c 0xffff8f81ffff062f 0xebfffe3e07fffc18

def z328 : W := mkw 0xddbd00009f280000 0x2376f400027ca000 0xffff00001f80000f 0xa3fffc00007e0000

def z329 : W := mkw 0x6bb6ff6c00000000 0x11aedbfdb0000000 0x01fffffe00000018 0x5007fffff8000000

def z330 : W := mkw 0x9e963d2c00000000 0x127a58f4b0000000 0x1e3f7c7e0000001e 0xb078fdf1f8000000

def z331 : W := mkw 0xf726fa64aa82d420 0x13dc9be992aa0b50 0xe6276070e380e002 0x0b989d81c38e0380

def z332 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e083f1e07f01c9 0x5387820fc781fc07

def z333 : W := mkw 0x6168c2d37477abde 0x0985a30b4dd1deaf 0xe1e0e3f1fc7ffffb 0xdf87838fc7f1ffff

def z334 : W := mkw 0x2000c00020028000 0x0080030000800a00 0x0000e0000003e010 0x4400038000000f80

def z335 : W := mkw 0x08d8008314610b52 0x002360020c51842d 0x19d800011c631fed 0xa467600004718c7f

def z336 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xe600e001e383e033 0xcf980380078e0f80

def z337 : W := mkw 0xffb6fffc2007a19c 0x1bfedbfff0801e86 0xfffffffe0003e1df 0xf7fffffff8000f87

def z338 : W := mkw 0xfdf4c801ee528420 0x23f7d32007b94a10 0xf9c08c01ec030601 0x63e7023007b00c18

def z339 : W := mkw 0x6323f274619ef08d 0x0d8c8fc9d1867bc2 0xe6276070e39ce002 0x0b989d81c38e7380

def z340 : W := mkw 0x9c9d050a9f280a42 0x227274142a7ca029 0x1e1f1c0e1f801e04 0x20787c70387e0078

def z341 : W := mkw 0x08d8059b7477abde 0x082360166dd1deaf 0x19d89f8ffc7ffffd 0xfc67627e3ff1ffff

def z342 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e063f0e07ce1ca 0x1b87818fc381f387

def z343 : W := mkw 0x08d8050b14600a42 0x002360142c518029 0x19d81c0f1c601e2d 0xa06760703c718078

def z344 : W := mkw 0xdfff3027dff85841 0x277ffcc09f7fe161 0xffff100ffffc182f 0xabfffc403ffff060

def z345 : W := mkw 0xffb6ff6caa028420 0x13fedbfdb2a80a10 0xffffffffec03061f 0xf3ffffffffb00c18

def z346 : W := mkw 0x2040c2d16057a19c 0x0881030b45815e86 0x0000e3f1e07fe1f0 0x5c00038fc781ff87

def z347 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff038ffffc01ef 0xbbfffc0e3ffff007

def z348 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x01d8838f006301f9 0xd407620e3c018c07

def z349 : W := mkw 0x2202ff6c2082d420 0x10880bfdb0820b50 0x0000fffe0003fe10 0x540003fff8000ff8

def z350 : W := mkw 0xfff6ffed04410312 0x13ffdbffb411040c 0xffffffff0c03061f 0xf3fffffffc300c18

def z351 : W := mkw 0x0000001000042088 0x0000000040001082 0x00000000007ce1e0 0x0c0000000001f387

def z352 : W := mkw 0x9c9400008e000000 0x2272500002380000 0x180000000c000000 0x2060000000300000

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x000060000000e032 0x8c00018000000380

def z354 : W := mkw 0xddb4000000000000 0x0376d00000000000 0xf9c0000000000001 0x23e7000000000000

def z355 : W := mkw 0x004000916057a19c 0x0801000245815e86 0x00206071e07fe1fa 0x9c008181c781ff87

def z356 : W := mkw 0xf726fa6400000000 0x13dc9be990000000 0xe7e7e3f00000001b 0xd39f9f8fc0000000

def z357 : W := mkw 0xd72f3036dbbc78c9 0x275cbcc0db6ef1e3 0xe63f707ef3fcf9fe 0x9f98fdc1fbcff3e7

def z358 : W := mkw 0x9ed83d8b9ee15f72 0x027b60f62e7b857d 0x1fd89f8f1fe31ffd 0xf47f627e3c7f8c7f

def z359 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x01d8138e106019fc 0x9407604e38418067

def z360 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xe7ff63fe0000000a 0x139ffd8ff8000000

def z361 : W := mkw 0x0002076c00000000 0x1000081db0000000 0x000003fe00000000 0x1000000ff8000000

def z362 : W := mkw 0xddbd000011280000 0x0376f4000044a000 0xffff000013fc002f 0xabfffc00004ff000

def z363 : W := mkw 0xd5650001cb580000 0x23559400072d6000 0xe7e70001e3fc002b 0x8b9f9c00078ff000

def z364 : W := mkw 0xfdfdc251ff7ea08c 0x2bf7f70947fdfa82 0xffff6071fffce02f 0xabfffd81c7fff380

def z365 : W := mkw 0xb400c000aa028000 0x02d0030002a80a00 0xfe00e001ff83e037 0xeff8038007fe0f80

def z366 : W := mkw 0x0008000210200840 0x0000200008408021 0x0018000e006001c8 0x1000600038018007

def z367 : W := mkw 0x08d9058b15690b52 0x002364162c55a42d 0x1fff9f8f1fff1fff 0xfc7ffe7e3c7ffc7f

def z368 : W := mkw 0xb600f80020028000 0x02d803e000800a00 0xfe00fc01e003e037 0xeff803f007800f80

def z369 : W := mkw 0x0009001211ac78c9 0x040024004846b1e3 0x063f000013fcf9ee 0x8c18fc00004ff3e7

def z370 : W := mkw 0x0202303400847089 0x040808c0d00211c2 0x000060700000e000 0x00000181c0000380

def z371 : W := mkw 0xffbfff7e112c28c9 0x17fefffdf844b0a3 0xfffffffe007c01df 0xf3fffffff801f007

def z372 : W := mkw 0xb400c800aa028420 0x02d0032002a80a10 0xe0000000e0000000 0x0380000003800000

def z373 : W := mkw 0xffffffff15ed7bdb 0x17fffffffc57b5ef 0xffffffff1fffffff 0xfffffffffc7fffff

def z374 : W := mkw 0xfffff2f7fffff9dd 0x2fffffcbdfffffe7 0xfffff3fffffff9ff 0xffffffcfffffffe7

def z375 : W := mkw 0x940500008b080000 0x22501400022c2000 0x0607000003800000 0x00181c00000e0000

def z376 : W := mkw 0xdffd3801dff85420 0x237ff4e0077fe150 0xffff1c01fffc1e2f 0xabfffc7007fff078

def z377 : W := mkw 0xddb6076c00000000 0x1376d81db0000000 0xffff03fe0000000f 0xb3fffc0ff8000000

def z378 : W := mkw 0x004800937477abde 0x080120024dd1deaf 0x00000001fc7fffe0 0x0c00000007f1ffff

def z379 : W := mkw 0xddfd0509df780000 0x2377f414277de000 0xffff9f8ffffc003f 0xfbfffe7e3ffff000

def z380 : W := mkw 0x0898050a14200a42 0x0022601428508029 0x19d89f8e1c001e1d 0xf067627e38700078

def z381 : W := mkw 0x4160001140542088 0x0105800045015082 0xe1e06071e07ce1fb 0x9f878181c781f387

def z382 : W := mkw 0xfff6fffdead7f5bc 0x1bffdbfff7ab5fd6 0xffffffffffffffff 0xffffffffffffffff

def z383 : W := mkw 0x9e9f3d3e11ac78c9 0x167a7cf4f846b1e3 0x1e3f7c7e13fcf9fe 0xbc78fdf1f84ff3e7

def z384 : W := mkw 0x2000c2502006a08c 0x0880030940801a82 0x000060700000e000 0x00000181c0000380

def z385 : W := mkw 0x96003800aa82d420 0x025800e002aa0b50 0x1e001c01ff83fe24 0x2c78007007fe0ff8

def z386 : W := mkw 0xffffff6d55780000 0x33fffffdb555e000 0xfffffffe007c001f 0xf3fffffff801f000

def z387 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffdf9f8e00000005 0x63ff7e7e38000000

def z388 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe009c01ff831e05 0x63f8027007fe0c78

def z389 : W := mkw 0x6360f2d160d7f19c 0x098d83cb45835fc6 0xe7e0f3f1f3fff9ff 0xdf9f83cfc7cfffe7

def z390 : W := mkw 0x00000000aa028420 0x0000000002a80a10 0x00000001ec030600 0x0000000007b00c18

def z391 : W := mkw 0x4160008140510110 0x0105800205014404 0xe1e08381e07f01fb 0xdf87820e0781fc07

def z392 : W := mkw 0x28d8c7db3467abde 0x08a3631f6cd19eaf 0x19d8ffff1c63fffd 0xf46763fffc718fff

def z393 : W := mkw 0x6160c2516056a08c 0x0985830945815a82 0xe1e06071e07ce02b 0x8b878181c781f380

def z394 : W := mkw 0x00010010018c7089 0x04000400400631c2 0x00000000039ce000 0x08000000000e7380

def z395 : W := mkw 0xfff6ffed60538114 0x1bffdbffb5814e04 0xffffffffe003001f 0xf3ffffffff800c00

def z396 : W := mkw 0x6160c2c160538114 0x0985830b05814e04 0xe1e0e3f1e003001b 0xd387838fc7800c00

def z397 : W := mkw 0x9e963d2c00000000 0x127a58f4b0000000 0x1fdf9f8e0000001d 0xf07f7e7e38000000

def z398 : W := mkw 0x0a9b352e15a85a43 0x042a6cd4b856a169 0x1e1f1c0e1f801e04 0x20787c70387e0078

def z399 : W := mkw 0x0a92352c00000000 0x002a48d4b0000000 0x1ffffffe0000001f 0xf07ffffff8000000

def z400 : W := mkw 0x00020036000428c9 0x04000800d80010a3 0x0000007e000001c0 0x10000001f8000007

def z401 : W := mkw 0x08d8058914610312 0x002360162451840c 0x19d88f811c63062d 0xe067623e04718c18

def z402 : W := mkw 0x6120c2506016a08c 0x0984830941805a82 0xe1e0e3f0e01ce01b 0xdb87838fc3807380

def z403 : W := mkw 0x0009001211ac78c9 0x040024004846b1e3 0x0018100e13fcf9fc 0x9c006040384ff3e7

def z404 : W := mkw 0x6160c00160528000 0x0185830005814a00 0xe1e0e001e07fe03b 0xcf8783800781ff80

def z405 : W := mkw 0x6160c2d14055219c 0x0985830b45015486 0xe1e0e3f0007c01db 0xd387838fc001f007

def z406 : W := mkw 0x6362fffd6057a19c 0x198d8bfff5815e86 0xe1e0ffffe07fe1fb 0xdf8783ffff81ff87

def z407 : W := mkw 0x2000c00020028000 0x0080030000800a00 0xf800fc01fc03fe37 0xefe003f007f00ff8

def z408 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xe600fc00e383fe12 0x4f9803f0038e0ff8

def z409 : W := mkw 0xddb4050800000000 0x0376d01420000000 0xffff9f8e0000001f 0xf3fffe7e38000000

def z410 : W := mkw 0x9e9e3d2e14200a42 0x127a78f4b8508029 0x1e1f1c0e1c001e04 0x20787c7038700078

def z411 : W := mkw 0x02023036008478c9 0x040808c0d80211e3 0x0020707e007cf9fa 0x9c0081c1f801f3e7

def z412 : W := mkw 0x416002d16057a19c 0x0905800b45815e86 0x01e003f1e07fe1e8 0x1c07800fc781ff87

def z413 : W := mkw 0x0898058a14210b52 0x002260162850842d 0x18189f8e1c031fd4 0x7460627e38700c7f

def z414 : W := mkw 0x0000058800010312 0x000000162000040c 0x00008f8000030600 0x4000023e00000c18

def z415 : W := mkw 0x0202302600805841 0x040808c098020161 0x0000100e00001800 0x0000004038000060

def z416 : W := mkw 0xfdb4cf4800000000 0x13f6d33d20000000 0xffff8f800000000f 0xe3fffe3e00000000

def z417 : W := mkw 0x00490091ff7fa19c 0x2801240247fdfe86 0x00000001ffffe1e0 0x0c00000007ffff87

def z418 : W := mkw 0x220bf2f631aff9dd 0x0c882fcbd8c6bfe7 0x063ff3fe13fff9fe 0xdc18ffcff84fffe7

def z419 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19c08f811c631fe1 0x6467023e04718c7f

def z420 : W := mkw 0x6360fad160d7f5bc 0x098d83eb45835fd6 0xe1e0fff1e07ffffb 0xdf8783ffc781ffff

def z421 : W := mkw 0x2000c00020028000 0x0080030000800a00 0xe0008001e0030001 0x4380020007800c00

def z422 : W := mkw 0xfff6ff6dce500000 0x33ffdbfdb7394000 0xffffffffec00001f 0xf3ffffffffb00000

def z423 : W := mkw 0x00490001df780000 0x20012400077de000 0x063f0001fffc002e 0x8818fc0007fff000

def z424 : W := mkw 0x0002002400000000 0x0000080090000000 0x003f007e00000008 0x1000fc01f8000000

def z425 : W := mkw 0x69f8c2d17477a19c 0x09a7e30b45d1de86 0xf9f8e3f1fc7fe1ff 0xffe7e38fc7f1ff87

def z426 : W := mkw 0x0202303400042088 0x000808c0d0001082 0x063f707e007ce1fe 0x9c18fdc1f801f387

def z427 : W := mkw 0xfdf4cfc960538114 0x1bf7d33f25814e04 0xf9c08f81e0030001 0x63e7023e07800c00

def z428 : W := mkw 0xfdfdc7dbff7fabde 0x2bf7f71f6ffdfeaf 0xffffffffffffffff 0xffffffffffffffff

def z429 : W := mkw 0x940000008a000000 0x0250000002280000 0xe6000000e3800002 0x0b980000038e0000

def z430 : W := mkw 0xb400c800aa028420 0x02d0032002a80a10 0xf8009c01fc031e35 0xe7e0027007f00c78

def z431 : W := mkw 0x4bb6376c00000000 0x112ed8ddb0000000 0x07ff73fe0000001e 0x901ffdcff8000000

def z432 : W := mkw 0x2000c00020028000 0x0080030000800a00 0xe0006000e000e002 0x0b80018003800380

def z433 : W := mkw 0x0200300000000000 0x000800c000000000 0x0600700000000016 0x801801c000000000

def z434 : W := mkw 0x960030008a805000 0x025800c0022a0140 0xfe007001ff80f837 0xaff801c007fe03e0

def z435 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1c08381e07fe1e1 0x4f87020e0781ff87

def z436 : W := mkw 0x0896052c00000000 0x10225814b0000000 0x001f000e00000000 0x00007c0038000000

def z437 : W := mkw 0xf560cad1ea57a5bc 0x0bd5832b47a95e96 0xf9e0eff1ec7fe7fb 0xffe783bfc7b1ff9f

def z438 : W := mkw 0x0898050a14200a42 0x0022601428508029 0x0018000e00000000 0x0000600038000000

def z439 : W := mkw 0xddf40001ce500000 0x2377d00007394000 0xffff0001ec00000f 0xa3fffc0007b00000

def z440 : W := mkw 0x0000001000042088 0x0000000040001082 0x00206070001ce002 0x08008181c0007380

def z441 : W := mkw 0xf725f800eb9ad420 0x23dc97e003ae6b50 0xe6276000e39ce002 0x0b989d80038e7380

def z442 : W := mkw 0xddfd0003df780840 0x2377f4000f7de021 0xffff100ffffc19ff 0xbffffc403ffff067

def z443 : W := mkw 0x00080012102428c8 0x00002000484090a3 0x0038707e107cf9fe 0x9c00e1c1f841f3e7

def z444 : W := mkw 0x0000000020028000 0x0000000000800a00 0x00000001e003e020 0x0c00000007800f80

def z445 : W := mkw 0x49ff076d55780000 0x3127fc1db555e000 0x01ff03fe007c0008 0x1007fc0ff801f000

def z446 : W := mkw 0x00030034010c2089 0x04000c00d0043082 0x00270070001c0000 0x00009c01c0007000

def z447 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d88f8f0c6307c9 0x7067623e3c318c1f

def z448 : W := mkw 0x9606382400000000 0x125818e090000000 0x0607000000000000 0x00181c0000000000

def z449 : W := mkw 0x0008000210200840 0x0000200008408021 0x0018100e10001804 0x0000604038400060

def z450 : W := mkw 0xf76bfaf7fbfffdfd 0x0fddafebdfeffff7 0xffffffffffffffff 0xffffffffffffffff

def z451 : W := mkw 0xf760f801ead2d420 0x03dd83e007ab4b50 0xffe0fc01fffffe3f 0xefff83f007fffff8

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x18009c0000000015 0xe060027000000000

def z453 : W := mkw 0x000000008a000000 0x0000000002280000 0x00000001ff800020 0x0800000007fe0000

def z454 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d8038f1c6001ed 0xb067600e3c718007

def z455 : W := mkw 0x0898050a10200840 0x0022601428408021 0x19d89f8e106019fd 0xf467627e38418067

def z456 : W := mkw 0xfff6ffed00410110 0x13ffdbffb4010404 0xffffffff006301ff 0xf7fffffffc018c07

def z457 : W := mkw 0xf720fa50ea96f4ac 0x0bdc83e943aa5bd2 0xe6206070e39ce002 0x0b988181c38e7380

def z458 : W := mkw 0xf525c250eb1ea08c 0x2bd4970943ac7a82 0xe6276070e39ce002 0x0b989d81c38e7380

def z459 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d89f8e006001dd 0xf067627e38018007

def z460 : W := mkw 0x9c940d0800000000 0x1272503420000000 0x18000c0000000000 0x2060003000000000

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x18001c001c001e04 0x2060007000700078

def z462 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe0206071e07fe1e2 0x0f808181c781ff87

def z463 : W := mkw 0x6160c2c100410110 0x0185830b04010404 0xe1e0e3f1006301fb 0xd787838fc4018c07

def z464 : W := mkw 0xb60bf83611ac78c9 0x06d82fe0d846b1e3 0xfe3ffc7e13fcf9ff 0xfff8fff1f84ff3e7

def z465 : W := mkw 0x6120c25000042088 0x0184830940001082 0xe1e0e3f0007ce1fb 0xdf87838fc001f387

def z466 : W := mkw 0x000000106016a08c 0x0800000041805a82 0x00000000e01ce000 0x0800000003807380

def z467 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x061f100e13fcf9e4 0x0c187c40384ff3e7

def z468 : W := mkw 0x0040008104410312 0x000100020411040c 0x000000010c030600 0x0000000004300c18

def z469 : W := mkw 0x6120c2d06017a19c 0x0984830b41805e86 0xe020e3f0e01fe1d2 0x5f80838fc3807f87

def z470 : W := mkw 0x020b302611a85841 0x04082cc09846a161 0x061f700e1380f836 0x8c187dc0384e03e0

def z471 : W := mkw 0x0048008314610b52 0x000120020c51842d 0x0018100f1c631ffc 0x940060403c718c7f

def z472 : W := mkw 0xffb4f80000000000 0x03fed3e000000000 0xfffffc000000001f 0xe3fffff000000000

def z473 : W := mkw 0x960038008a805420 0x025800e0022a0150 0x1e007c001f80fe36 0xac7801f0007e03f8

def z474 : W := mkw 0x2000c7da2007abde 0x0880031f68801eaf 0x0000fffe0003ffd0 0x540003fff8000fff

def z475 : W := mkw 0x416002d14055219c 0x0905800b45015486 0x01e083f1007f01f9 0xd407820fc401fc07

def z476 : W := mkw 0x0898050a14200a42 0x0022601428508029 0x18189c0f1c031e35 0xe46062703c700c78

def z477 : W := mkw 0xb602ff6caa82d420 0x12d80bfdb2aa0b50 0xfe00ffffff83fe37 0xfff803fffffe0ff8

def z478 : W := mkw 0x0040009100452198 0x0001000244011486 0x01e0e3f1007fe1fb 0xdc07838fc401ff87

def z479 : W := mkw 0x0000001000042088 0x0000000040001082 0x000060700000e1d0 0x14000181c0000387

def z480 : W := mkw 0x0048008314610b52 0x000120020c51842d 0x00000000006001c0 0x0000000000018007

def z481 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe00fc00e380e017 0xebf803f0038e0380

def z482 : W := mkw 0xb600f8008a805420 0x02d803e0022a0150 0xfe00fc001f801e17 0xe3f803f0007e0078

def z483 : W := mkw 0xfffeffef14610b52 0x13fffbffbc51842d 0xfffffffe006001df 0xf3fffffff8018007

def z484 : W := mkw 0x940000008a000000 0x0250000002280000 0xfe009c01ff831e37 0xeff8027007fe0c78

def z485 : W := mkw 0x49f607fd4055219c 0x1927d81ff5015486 0x01ff03fe007c01c8 0x1007fc0ff801f007

def z486 : W := mkw 0x416002d14055219c 0x0905800b45015486 0x01e063f0007ce1fa 0x9c07818fc001f387

def z487 : W := mkw 0x0048008310610950 0x000120020c418425 0x01d8938f106319fd 0xd407624e3c418c67

def z488 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x0627607013fcf9e2 0x0c189d81c04ff3e7

def z489 : W := mkw 0xb600f80000000000 0x02d803e000000000 0xe600600000000002 0x0398018000000000

def z490 : W := mkw 0xbe90fd08aa82d420 0x02fa43f422aa0b50 0xffd8ff8fff83fe3f 0xffff63fe3ffe0ff8

def z491 : W := mkw 0x020b302411280000 0x00082cc09044a000 0x063f707e13fc003e 0x9818fdc1f84ff000

def z492 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe006001ff80e027 0xabf8018007fe0380

def z493 : W := mkw 0x2000c00000000000 0x0080030000000000 0xe000e00000000013 0xc380038000000000

def z494 : W := mkw 0x0040008100410110 0x0001000204010404 0x19c09f811c631ffd 0xf467027e04718c7f

def z495 : W := mkw 0x004000916057a19c 0x0801000245815e86 0x01c08381e07fe1f9 0xdc07020e0781ff87

def z496 : W := mkw 0x940900009b280000 0x02502400026ca000 0xfe3f0001fffc002f 0xabf8fc0007fff000

def z497 : W := mkw 0x28d8c58b34638b52 0x00a363162cd18e2d 0xf9d8ff8ffc63ffff 0xffe763fe3ff18fff

def z498 : W := mkw 0x6160c2c160538114 0x0985830b05814e04 0xe1c0e381e003e033 0xcf87038e07800f80

def z499 : W := mkw 0xb400c80000000000 0x02d0032000000000 0xf8008c0000000001 0x63e0023000000000

def z500 : W := mkw 0xfdfdcf49df780000 0x33f7f73d277de000 0xffff8f81fffc002f 0xebfffe3e07fff000

def z501 : W := mkw 0x020b35be11ad7bdb 0x04082cd6f846b5ef 0x063ffffe13fffffe 0xdc18fffff84fffff

def z502 : W := mkw 0x2200fad02087f5bc 0x088803eb40821fd6 0x0000fff00003ffd0 0x540003ffc0000fff

def z503 : W := mkw 0x000000902007a19c 0x0800000240801e86 0x000000000003e1c0 0x0400000000000f87

def z504 : W := mkw 0xfdfdc241df780000 0x23f7f709077de000 0xffffe3f1fffc003f 0xfbffff8fc7fff000

def z505 : W := mkw 0x41690001df780000 0x2105a400077de000 0xe1e00001fffc002b 0x8b87800007fff000

def z506 : W := mkw 0xb603f834ab8ef4a9 0x06d80fe0d2ae3bd2 0xfe27fc71ff9ffe37 0xeff89ff1c7fe7ff8

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x063f00000000000e 0x8018fc0000000000

def z508 : W := mkw 0x00490083df790b52 0x200124020f7de42d 0x00000001ffff1fe0 0x0c00000007fffc7f

def z509 : W := mkw 0x2200f8002082d420 0x008803e000820b50 0x0600fc001383fe36 0xcc1803f0004e0ff8

def z510 : W := mkw 0xddfd0001fffad420 0x2377f40007ffeb50 0xffff0001fffffe2f 0xaffffc0007fffff8

def z511 : W := mkw 0xddfc058b14610b52 0x0377f0162c51842d 0xffff9f8f1c631fff 0xf7fffe7e3c718c7f

def z512 : W := mkw 0x0898050a14200a42 0x0022601428508029 0x18181c0e1c601ffc 0xb46060703871807f

def z513 : W := mkw 0xf725f800eb9ad420 0x23dc97e003ae6b50 0xfe27fc01ff9ffe37 0xeff89ff007fe7ff8

def z514 : W := mkw 0x000000002082d420 0x0000000000820b50 0x000000000003fe00 0x0400000000000ff8

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000013800026 0x88180000004e0000

def z516 : W := mkw 0xfdfdc001ff7a8000 0x23f7f70007fdea00 0xffffe001ffffe03f 0xefffff8007ffff80

def z517 : W := mkw 0x2000c2c020038114 0x0880030b00800e04 0x0000838000030000 0x4000020e00000c00

def z518 : W := mkw 0x0000000200000840 0x0000000008000021 0x0000100e000019d0 0x1400004038000067

def z519 : W := mkw 0xfdfdc2c1ff7b8114 0x2bf7f70b07fdee04 0xffff8381ffff002f 0xebfffe0e07fffc00

def z520 : W := mkw 0x69f0c7c964538316 0x09a7c31f25914e0c 0xf9c08f81ec030601 0x63e7023e07b00c18

def z521 : W := mkw 0x000000008a805420 0x00000000022a0150 0x000000001f801e00 0x00000000007e0078

def z522 : W := mkw 0x6120c2506016a08c 0x0984830941805a82 0xe020e071e01fe033 0xcf808381c7807f80

def z523 : W := mkw 0xddfd02d1df7d219c 0x2b77f40b477df486 0xffff03f1fffc01ef 0xbbfffc0fc7fff007

def z524 : W := mkw 0xfffff837fffefce9 0x27ffffe0dffffbf3 0xfffffc7fffffffff 0xfffffff1ffffffff

def z525 : W := mkw 0x9e9f30269fa85841 0x267a7cc09a7ea161 0x1e1f100e1f801804 0x20787c40387e0060

def z526 : W := mkw 0xb602ff6c00000000 0x12d80bfdb0000000 0xfe00fffe00000017 0xf3f803fff8000000

def z527 : W := mkw 0x0040008160538114 0x0801000205814e04 0x00000001e0030000 0x0000000007800c00

def z528 : W := mkw 0x0040000100400000 0x0001000004010000 0x01c0000100600029 0x8007000004018000

def z529 : W := mkw 0xbed8fd8b14610b52 0x02fb63f62c51842d 0xffd8ff8f1c631fff 0xf7ff63fe3c718c7f

def z530 : W := mkw 0xf760fad1ead7f5bc 0x0bdd83eb47ab5fd6 0xe7e0e3f1e3ffe1fb 0xdf9f838fc78fff87

def z531 : W := mkw 0x0200380000805420 0x000800e000020150 0x00001c0000001e00 0x0000007000000078

def z532 : W := mkw 0xb640f891ead7f5bc 0x0ad903e247ab5fd6 0xfe00fc01fffffff7 0xeff803f007ffffff

def z533 : W := mkw 0x6160c2c160538114 0x0985830b05814e04 0xe1c08381e06301f9 0xd787020e07818c07

def z534 : W := mkw 0xb400c800aa028420 0x02d0032002a80a10 0xfe008c01ff830627 0xebf8023007fe0c18

def z535 : W := mkw 0xddfc058bde710b52 0x2377f0162f79c42d 0xf9d89f8ffc631ffd 0xf7e7627e3ff18c7f

def z536 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000001e0000023 0x8b80000007800000

def z537 : W := mkw 0xfdf4c2d1ee57a19c 0x2bf7d30b47b95e86 0xf9e0e3f1ec7fe1fb 0xffe7838fc7b1ff87

def z538 : W := mkw 0xb600f80000000000 0x02d803e000000000 0xfe00fc011c031e37 0xe7f803f004700c78

def z539 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff9c01ffff1e3f 0xeffffe7007fffc78

def z540 : W := mkw 0xbe90fd0800000000 0x02fa43f420000000 0xffd8ff8e0000001f 0xf3ff63fe38000000

def z541 : W := mkw 0x49f4000144500000 0x2127d00005114000 0x01c0000000000000 0x0007000000000000

def z542 : W := mkw 0x9cdd0001df780000 0x22737400077de000 0x1e1f0001fffc0024 0x28787c0007fff000

def z543 : W := mkw 0x08d0058904410312 0x002340162411040c 0x19c09f811c031e35 0xe467027e04700c78

def z544 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f707e139cf806 0x0818fdc1f84e73e0

def z545 : W := mkw 0x4120000000000000 0x0104800000000000 0xe1e000000000000b 0x8387800000000000

def z546 : W := mkw 0x9ede3daf14610b52 0x127b78f6bc51842d 0x1fdf9f8f1c631ffd 0xf47f7e7e3c718c7f

def z547 : W := mkw 0x0008000210200840 0x0000200008408021 0x00000000106019e0 0x0400000000418067

def z548 : W := mkw 0x49b4074800000000 0x1126d01d20000000 0x01c0038000000000 0x0007000e00000000

def z549 : W := mkw 0xbcd8cd8bbe638f72 0x02f363362ef98e3d 0xf9d89f8ffc631ffd 0xf7e7627e3ff18c7f

def z550 : W := mkw 0xd524000000000000 0x0354900000000000 0xe627000000000002 0x03989c0000000000

def z551 : W := mkw 0xfdf4c2d16057a19c 0x0bf7d30b45815e86 0xffffe3f1e07fe1ff 0xffffff8fc781ff87

def z552 : W := mkw 0xdfff3035dffc7089 0x277ffcc0d77ff1c2 0xffff6071fffce02f 0xabfffd81c7fff380

def z553 : W := mkw 0x000b0036112c28c9 0x04002c00d844b0a3 0x003f607e007ce1fa 0x9c00fd81f801f387

def z554 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xf9c00001fffc0021 0x2be7000007fff000

def z555 : W := mkw 0x6169c2d371fff9dd 0x0d85a70b4dc7ffe7 0xe1e0e3f1f3fff9fb 0xdf87838fc7cfffe7

def z556 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffe7eff000000003 0x63ff9fbfc0000000

def z557 : W := mkw 0x000b002611280841 0x04002c009844a021 0x001f000e00000000 0x00007c0038000000

def z558 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe007c00ff80fe06 0x2bf801f003fe03f8

def z559 : W := mkw 0x6120c2506016a08c 0x0984830941805a82 0xe0206070e07ce1fa 0x9f808181c381f387

def z560 : W := mkw 0xb60bf826bbaadc61 0x06d82fe09aeeab71 0xfe1ffc0fff83fe37 0xeff87ff03ffe0ff8

def z561 : W := mkw 0x0000000000805000 0x0000000000020140 0x000000001380f820 0x0c000000004e03e0

def z562 : W := mkw 0xfdb6cf6c00000000 0x13f6db3db0000000 0xf9ff8ffe00000009 0x73e7fe3ff8000000

def z563 : W := mkw 0x416002d14055219c 0x0905800b45015486 0xe1e003f1e07c01eb 0x9b87800fc781f007

def z564 : W := mkw 0xbe98fd0abea2de62 0x02fa63f42afa8b79 0xfe18fc0fff83fe37 0xeff863f03ffe0ff8

def z565 : W := mkw 0x220bf83631aefce9 0x04882fe0d8c6bbf3 0x063ffc7e13fffffe 0xdc18fff1f84fffff

def z566 : W := mkw 0x08d0058904410312 0x002340162411040c 0x19d89f8f0c03061d 0xf067627e3c300c18

def z567 : W := mkw 0x0008000010200000 0x0000200000408000 0x001800001060002c 0x8000600000418000

def z568 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x061f707e1380f9d4 0x14187dc1f84e03e7

def z569 : W := mkw 0xddf40589ce510312 0x2377d0162739440c 0xf9c08f81ec030601 0x63e7023e07b00c18

def z570 : W := mkw 0x089d000015280000 0x202274000054a000 0x001f000000000000 0x00007c0000000000

def z571 : W := mkw 0xfdb4c24000000000 0x03f6d30900000000 0xffffe3f00000001f 0xf3ffff8fc0000000

def z572 : W := mkw 0x6160c2c160538114 0x0985830b05814e04 0xe1e08381e07f002b 0xcb87820e0781fc00

def z573 : W := mkw 0x0040008100410110 0x0001000204010404 0x01c00380006001c8 0x1007000e00018007

def z574 : W := mkw 0xb602f82400000000 0x02d80be090000000 0xfe3ffc7e0000001f 0xf3f8fff1f8000000

def z575 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xe6006001ff83fe22 0x0f98018007fe0ff8

def z576 : W := mkw 0x49fd02d1557d219c 0x2927f40b4555f486 0x01ff03f0007c01c8 0x1007fc0fc001f007

def z577 : W := mkw 0xf560c2d1ea57a19c 0x0bd5830b47a95e86 0xffe0e3f1ffffe1ff 0xffff838fc7ffff87

def z578 : W := mkw 0x08d8000114600000 0x0023600004518000 0x19d89c011c631e3d 0xe467627004718c78

def z579 : W := mkw 0x0202302400000000 0x000808c090000000 0x061f100e00000004 0x00187c4038000000

def z580 : W := mkw 0xffffffff71fff9dd 0x1ffffffffdc7ffe7 0xfffffffff3fff9ff 0xffffffffffcfffe7

def z581 : W := mkw 0x2000c24000000000 0x0080030900000000 0x0000e3f000000010 0x5000038fc0000000

def z582 : W := mkw 0x0009001211ac78c9 0x040024004846b1e3 0x0020607013fcf9fa 0x9c008181c04ff3e7

def z583 : W := mkw 0x49fd000155780000 0x2127f4000555e000 0x07ff000013fc002e 0x881ffc00004ff000

def z584 : W := mkw 0xb640f881aac3d530 0x02d903e206ab0f54 0xffc0ff81ffe3ffff 0xffff03fe07ff8fff

def z585 : W := mkw 0x960038008a805420 0x025800e0022a0150 0xfe001c01ff801e27 0xabf8007007fe0078

def z586 : W := mkw 0x49ff0037557c28c9 0x2527fc00dd55f0a3 0x01ff007e007c01c8 0x1007fc01f801f007

def z587 : W := mkw 0x024b30b771fff9dd 0x0c092cc2ddc7ffe7 0x063f707ff3fff9fe 0x9c18fdc1ffcfffe7

def z588 : W := mkw 0xf726ff6c00000000 0x13dc9bfdb0000000 0xe627fffe00000012 0x53989ffff8000000

def z589 : W := mkw 0x4160000140500000 0x0105800005014000 0x01e00000007c0008 0x000780000001f000

def z590 : W := mkw 0x6bfbf7ff75fffbdf 0x0dafefdffdd7ffef 0xffffffffffffffff 0xffffffffffffffff

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200000007c002a 0x880080000001f000

def z592 : W := mkw 0xffffff7fdffc78c9 0x37fffffdff7ff1e3 0xfffffffffffcf9ff 0xfffffffffffff3e7

def z593 : W := mkw 0x49bf077e112c28c9 0x1526fc1df844b0a3 0x01ff03fe007c01c8 0x1007fc0ff801f007

def z594 : W := mkw 0xfdf4cf49ce500000 0x33f7d33d27394000 0xf9c08f81ec000001 0x63e7023e07b00000

def z595 : W := mkw 0x6169c2d1717fa19c 0x0985a70b45c5fe86 0xe7ffe3f1f3ffe1ff 0xdf9fff8fc7cfff87

def z596 : W := mkw 0x02033036018c78c9 0x04080cc0d80631e3 0x0627707e039cf9d2 0x1c189dc1f80e73e7

def z597 : W := mkw 0x00400091ead7f5bc 0x0801000247ab5fd6 0x00000001ffffffe0 0x0c00000007ffffff

def z598 : W := mkw 0xffbfff6c9f280000 0x33fefffdb27ca000 0xfffffffe1f80001f 0xf3fffffff87e0000

def z599 : W := mkw 0x9cdd00019f680000 0x22737400067da000 0x1fdf00011fe0002d 0xa07f7c00047f8000

def z600 : W := mkw 0xf760fac1ead3d534 0x0bdd83eb07ab4f54 0xffc0ff81ff83fe37 0xefff03fe07fe0ff8

def z601 : W := mkw 0x00490013dffc78c9 0x240124004f7ff1e3 0x00000001fffcf9e0 0x0c00000007fff3e7

def z602 : W := mkw 0x2202ff7e008478c9 0x14880bfdf80211e3 0x0000fffe0000f9d0 0x540003fff80003e7

def z603 : W := mkw 0x4126026400000000 0x1104980990000000 0x0027007000000000 0x00009c01c0000000

def z604 : W := mkw 0xffb4ff4800000000 0x13fed3fd20000000 0xffc0ff8000000017 0xe3ff03fe00000000

def z605 : W := mkw 0x9e9f3d2e11a85841 0x167a7cf4b846a161 0x1e1f1c0e13801804 0x20787c70384e0060

def z606 : W := mkw 0x020b3036112c28c9 0x04082cc0d844b0a3 0x063f707e007c01de 0x9018fdc1f801f007

def z607 : W := mkw 0x0adb35af15e95b53 0x042b6cd6bc57a56d 0x1fdf9f8f1fe31ffd 0xf47f7e7e3c7f8c7f

def z608 : W := mkw 0xb602f836aa86fce9 0x06d80be0daaa1bf3 0xfe00fc7fff83fff7 0xfff803f1fffe0fff

def z609 : W := mkw 0x69b0c74800000000 0x01a6c31d20000000 0xf9f8fffe0000001f 0xf3e7e3fff8000000

def z610 : W := mkw 0x0200301000847088 0x000800c0400211c2 0x0620707013fcf9fe 0x9c1881c1c04ff3e7

def z611 : W := mkw 0x08d8058bbee3df72 0x002360162efb8f7d 0x19d89f8fffe3fffd 0xfc67627e3fff8fff

def z612 : W := mkw 0xfdf4cfd96057a19c 0x1bf7d33f65815e86 0xf9e0eff1e07fe1fb 0xffe783bfc781ff87

def z613 : W := mkw 0xfff8ffdbfef7fffe 0x0bffe3ff6ffbdfff 0xfff8ffffffffffff 0xffffe3ffffffffff

def z614 : W := mkw 0xddf4000140500000 0x0377d00005014000 0xffff0001e07c002f 0xabfffc000781f000

def z615 : W := mkw 0x0200300000805000 0x000800c000020140 0x0600100013801804 0x00180040004e0060

def z616 : W := mkw 0x08d8000314600840 0x002360000c518021 0x19d8100f1c6019fd 0xb46760403c718067

def z617 : W := mkw 0x02033034018c7089 0x04080cc0d00631c2 0x063f707e039ce01e 0x9818fdc1f80e7380

def z618 : W := mkw 0x0200300000805000 0x000800c000020140 0x1e00fc011f83fe37 0xec7803f0047e0ff8

def z619 : W := mkw 0xffb6fa6400000000 0x13fedbe990000000 0xffff60700000000f 0xa3fffd81c0000000

def z620 : W := mkw 0x2200f8002082d420 0x008803e000820b50 0x1800fc011c03fe35 0xe46003f004700ff8

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000006001f8 0x9400000000018007

def z622 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xf9c0fffe00000011 0x73e703fff8000000

def z623 : W := mkw 0x0040008100410110 0x0001000204010404 0x01c0838100030001 0x4007020e04000c00

def z624 : W := mkw 0x08d0058900410110 0x0023401624010404 0x19d89f8f006301fd 0xf467627e3c018c07

def z625 : W := mkw 0x6363f2f561dff19d 0x0d8d8fcbd5877fc6 0xe7e7e3f1e3ffe1fb 0xdf9f9f8fc78fff87

def z626 : W := mkw 0x0200300000805000 0x000800c000020140 0x000070000000f810 0x040001c0000003e0

def z627 : W := mkw 0xb600f800aa028420 0x02d803e002a80a10 0xfe00fc01ec030617 0xe3f803f007b00c18

def z628 : W := mkw 0xfff6fffd4055219c 0x1bffdbfff5015486 0xfffffffe007c01df 0xf3fffffff801f007

def z629 : W := mkw 0x9cdd058b9f690b52 0x227374162e7da42d 0x1fdf9f8f1fe31ffd 0xf47f7e7e3c7f8c7f

def z630 : W := mkw 0xf727fa64cb180000 0x33dc9fe9932c6000 0xe6276070e39c0002 0x0b989d81c38e7000

def z631 : W := mkw 0x0ada35bf14e57bdb 0x042b68d6fc5395ef 0x19d8ffff1c63fffd 0xf46763fffc718fff

def z632 : W := mkw 0x2200f8002082d420 0x008803e000820b50 0xe000fc01e003fe33 0xcf8003f007800ff8

def z633 : W := mkw 0xdfff3d2ddf780000 0x337ffcf4b77de000 0xffff1c0ffffc002f 0xabfffc703ffff000

def z634 : W := mkw 0x0a9b353e15ac7acb 0x042a6cd4f856b1eb 0x1e3f7c7e1ffcfffe 0xbc78fdf1f87ff3ff

def z635 : W := mkw 0xbe9df800bfaad420 0x22fa77e002feab50 0xfe1ffc01ff83fe37 0xeff87ff007fe0ff8

def z636 : W := mkw 0x9cd800019e600000 0x0273600006798000 0xffd80001ffe0002f 0xabff600007ff8000

def z637 : W := mkw 0x960b30369bac78c9 0x06582cc0da6eb1e3 0xfe3f707ffffcf9ff 0xbff8fdc1fffff3e7

def z638 : W := mkw 0xb649f801fffad420 0x22d927e007ffeb50 0xfe00fc01fffffe37 0xeff803f007fffff8

def z639 : W := mkw 0xfdb4cf4800000000 0x13f6d33d20000000 0xf9d89f8e0000001d 0xf3e7627e38000000

def z640 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xf9ff0001ec7c0009 0x23e7fc0007b1f000

def z641 : W := mkw 0x2000c80020028420 0x0080032000800a10 0x00008c0000030600 0x4000023000000c18

def z642 : W := mkw 0x6160c24140500000 0x0185830905014000 0xe1e0e3f1e07c003b 0xdb87838fc781f000

def z643 : W := mkw 0xb603f834ab8ef4a9 0x06d80fe0d2ae3bd2 0xe6276070e39ce002 0x0b989d81c38e7380

def z644 : W := mkw 0xffb6ff7c6016a08c 0x1bfedbfdf1805a82 0xfffffffee01ce01f 0xfbfffffffb807380

def z645 : W := mkw 0x2000c0102006a088 0x0080030040801a82 0xe020e071e07fe1fb 0xdf808381c781ff87

def z646 : W := mkw 0x436b303751fc78c9 0x050dacc0dd47f1e3 0xe7ff707ff3fcf9ff 0x9f9ffdc1ffcff3e7

def z647 : W := mkw 0x08d0058904410312 0x002340162411040c 0x01c0038000000000 0x0007000e00000000

def z648 : W := mkw 0x020b303411ac7089 0x04082cc0d046b1c2 0x063f607013fce02e 0x8818fd81c04ff380

def z649 : W := mkw 0x6120c24000000000 0x0184830900000000 0xe1c0838000000001 0x4387020e00000000

def z650 : W := mkw 0xb648f883bee3df72 0x02d923e20efb8f7d 0xfe00fc01ffe3fff7 0xeff803f007ff8fff

def z651 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x003f707e007cf9d8 0x1400fdc1f801f3e7

def z652 : W := mkw 0x220bff7e11ac78c9 0x14882ffdf846b1e3 0x063ffffe13fcf9fe 0xdc18fffff84ff3e7

def z653 : W := mkw 0xb60bf836bbaefce9 0x06d82fe0daeebbf3 0xe63f707ef3fcf9fe 0x9f98fdc1fbcff3e7

def z654 : W := mkw 0xddfd0011df7c2088 0x2377f400477df082 0xffff6071fffce1ff 0xbffffd81c7fff387

def z655 : W := mkw 0x69fdc2d1757fa19c 0x29a7f70b45d5fe86 0xe1ffe3f1e07fe1fb 0xdf87ff8fc781ff87

def z656 : W := mkw 0xf760fad16057a19c 0x0bdd83eb45815e86 0xffe0fff1e07fe1ff 0xffff83ffc781ff87

def z657 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x0000707e13fcf9f0 0x1c0001c1f84ff3e7

def z658 : W := mkw 0x6169c2d1ff7fa19c 0x2985a70b47fdfe86 0xe1e0e3f1ffffe1fb 0xdf87838fc7ffff87

def z659 : W := mkw 0x2adaffef14610b52 0x10ab6bffbc51842d 0x19d8ffff1c631ffd 0xf46763fffc718c7f

def z660 : W := mkw 0xf726fa6400000000 0x13dc9be990000000 0xe63f707e0000001e 0x9398fdc1f8000000

def z661 : W := mkw 0x0890000000000000 0x0022400000000000 0x19d800000000000d 0xa067600000000000

def z662 : W := mkw 0xf560cac1ea538534 0x0bd5832b07a94e14 0xf9c08f81ec030601 0x63e7023e07b00c18

def z663 : W := mkw 0x9cd8058b9e610b52 0x027360162e79842d 0xffd89f8fffe31fff 0xffff627e3fff8c7f

def z664 : W := mkw 0x08d8008114610110 0x0023600204518404 0x19d883811c6301fd 0xf467620e04718c07

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000800100030031 0xc400020004000c00

def z666 : W := mkw 0x960b38369bac7ce9 0x06582ce0da6eb1f3 0x1e3f7c7e1ffcfffe 0xbc78fdf1f87ff3ff

def z667 : W := mkw 0xddfd0091ff7fa19c 0x2b77f40247fdfe86 0xffff0001ffffe1ef 0xaffffc0007ffff87

def z668 : W := mkw 0xffb4ff48aa82d420 0x13fed3fd22aa0b50 0xffc0ff81ff83fe37 0xefff03fe07fe0ff8

def z669 : W := mkw 0x00000012008478c9 0x04000000480211e3 0x000000000000f9c0 0x04000000000003e7

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x00009c0000031e10 0x4400027000000c78

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000011c031e20 0x0400000004700c78

def z672 : W := mkw 0xbcd0cd89ae438732 0x02f3433626b90e1c 0xf9c08f81ec030601 0x63e7023e07b00c18

def z673 : W := mkw 0x08d8050914600000 0x0023601424518000 0x19d89f8f1c60003d 0xf067627e3c718000

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018100e0000001c 0x9000604038000000

def z675 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xe6007000f380f836 0x8f9801c003ce03e0

def z676 : W := mkw 0x49fe07ef14610b52 0x1127f81fbc51842d 0x01ff03fe006001c8 0x1007fc0ff8018007

def z677 : W := mkw 0x000b0036112c28c9 0x04002c00d844b0a3 0x063f007e13fc01ee 0x9818fc01f84ff007

def z678 : W := mkw 0xffb4f800aa82d420 0x03fed3e002aa0b50 0xfffffc01ff83fe3f 0xeffffff007fe0ff8

def z679 : W := mkw 0x02023d2c00000000 0x100808f4b0000000 0x00001c0e00000000 0x0000007038000000

def z680 : W := mkw 0xbedbfdbfbfeffffb 0x06fb6ff6feffbfff 0xffffffffffffffff 0xffffffffffffffff

def z681 : W := mkw 0x49f8058b54710b52 0x0127e0162d51c42d 0xf9f89f8ffc7f1fff 0xffe7e27e3ff1fc7f

def z682 : W := mkw 0x024b3037dffc78c9 0x24092cc0df7ff1e3 0x063f707ffffcf9fe 0x9c18fdc1fffff3e7

def z683 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffdf0001ff800005 0x23ff7c0007fe0000

def z684 : W := mkw 0xf720fa4000000000 0x03dc83e900000000 0xffe0fff00000001f 0xf3ff83ffc0000000

def z685 : W := mkw 0x020b302611a85841 0x04082cc09846a161 0x063f100e13fc182e 0x8818fc40384ff060

def z686 : W := mkw 0xffb6ff7c00042088 0x13fedbfdf0001082 0xfffffffe007ce1ff 0xfffffffff801f387

def z687 : W := mkw 0x412002504014208c 0x0904800941005082 0x00200070001c0000 0x00008001c0007000

def z688 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xf800fc01ec03fe11 0x67e003f007b00ff8

def z689 : W := mkw 0x08d8000114600000 0x0023600004518000 0x01d8000000600008 0x0007600000018000

def z690 : W := mkw 0x2ad8fd8b34e3df72 0x00ab63f62cd38f7d 0x19d8ff8f1c63fffd 0xf46763fe3c718fff

def z691 : W := mkw 0x0000001000042088 0x0000000040001082 0x00200070007c01c8 0x10008001c001f007

def z692 : W := mkw 0x0890050800000000 0x0022401420000000 0x18181c0e00000004 0x2060607038000000

def z693 : W := mkw 0x2200f800aa82d420 0x008803e002aa0b50 0x0000fc01ff83fe30 0x4c0003f007fe0ff8

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x002060700000001a 0x90008181c0000000

def z695 : W := mkw 0xb609f800bbaad420 0x02d827e002eeab50 0xfe3ffc01fffffe3f 0xeff8fff007fffff8

def z696 : W := mkw 0xb600f8002082d420 0x02d803e000820b50 0xfe00fc000003fe17 0xe7f803f000000ff8

def z697 : W := mkw 0x00090012bbaefce9 0x040024004aeebbf3 0x00000001ffffffe0 0x0c00000007ffffff

def z698 : W := mkw 0x940000008a000000 0x0250000002280000 0xf8000001ec000001 0x23e0000007b00000

def z699 : W := mkw 0xb600fad0aa87f5bc 0x0ad803eb42aa1fd6 0xfe00fff1ff83fff7 0xfff803ffc7fe0fff

def z700 : W := mkw 0xdfb63d2c00000000 0x137ed8f4b0000000 0xffff1c0e0000000f 0xa3fffc7038000000

def z701 : W := mkw 0x0048058b14610b52 0x000120162c51842d 0x00009f8f1c631ff0 0x5400027e3c718c7f

def z702 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0x1e00fc001f83fe14 0x647803f0007e0ff8

def z703 : W := mkw 0xddfd000155780000 0x2377f4000555e000 0xffff0000007c000f 0xa3fffc000001f000

def z704 : W := mkw 0x08d0058904410312 0x002340162411040c 0x19c08f810c6307f9 0xf467023e04318c1f

def z705 : W := mkw 0x49f8000154700000 0x0127e0000551c000 0xf9f80001fc7c002f 0xabe7e00007f1f000

def z706 : W := mkw 0x02033034018c7089 0x04080cc0d00631c2 0x0627607003fce1fa 0x9c189d81c00ff387

def z707 : W := mkw 0xddfd050bdf780840 0x2377f4142f7de021 0xffff9f8ffffc19ff 0xfffffe7e3ffff067

def z708 : W := mkw 0x6bb6ff6c00000000 0x11aedbfdb0000000 0x19fffffe0000001d 0xf067fffff8000000

def z709 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff8381fffc003f 0xfbfffe0e07fff000

def z710 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d89f8f1c631fcd 0x7067627e3c718c7f

def z711 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19c09f8f1c631ff1 0x7467027e3c718c7f

def z712 : W := mkw 0x49b6076caa82d420 0x1126d81db2aa0b50 0x01ff03ffff83fe28 0x1c07fc0ffffe0ff8

def z713 : W := mkw 0x4169008351790950 0x0105a4020d45e425 0xe7ff938ff3ff19ff 0xdf9ffe4e3fcffc67

def z714 : W := mkw 0xffb6ff6c8a805000 0x13fedbfdb22a0140 0xffffffffff80f83f 0xfffffffffffe03e0

def z715 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xe6270000f39c0026 0x8b989c0003ce7000

def z716 : W := mkw 0xb40bc836bb2eace9 0x06d02f20daecbab3 0xf83f8c7fec7f07c9 0x73e0fe31ffb1fc1f

def z717 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1c0e3f1e07fe1f1 0x5f87038fc781ff87

def z718 : W := mkw 0xfdbdcf5a11ac78c9 0x17f6f73d6846b1e3 0xf9c08f8013fcf9e1 0x6fe7023e004ff3e7

def z719 : W := mkw 0xddfd0083df790b52 0x2377f4020f7de42d 0xffff0001fffc01ef 0xabfffc0007fff007

def z720 : W := mkw 0x08d0058b04410b52 0x002340162c11042d 0x19d89f8f0c031fdd 0xf467627e3c300c7f

def z721 : W := mkw 0x08d0058900410110 0x0023401624010404 0x19d89f8f1c631ffd 0xf467627e3c718c7f

def z722 : W := mkw 0xd56d0001df780000 0x2355b400077de000 0xfe270001fffc0027 0xabf89c0007fff000

def z723 : W := mkw 0xddfd0509df780000 0x2377f414277de000 0xffff8f81fffc002f 0xebfffe3e07fff000

def z724 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d89f8f1c631fe5 0x6467627e3c718c7f

def z725 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xfe270001ef9c0003 0x2bf89c0007be7000

def z726 : W := mkw 0xf76efae714610b52 0x13ddbbeb9c51842d 0xe62760711c631fe2 0x07989d81c4718c7f

def z727 : W := mkw 0xf727fa74ab8ef4a9 0x17dc9fe9d2ae3bd2 0xe6276070e39ce002 0x0b989d81c38e7380

def z728 : W := mkw 0xfdf4cfc9ea538534 0x1bf7d33f27a94e14 0xf9c08f81ec030601 0x63e7023e07b00c18

def z729 : W := mkw 0x224bff6ddf780000 0x30892ffdb77de000 0x0000fffffffc0030 0x580003fffffff000

def z730 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d89f8f0c631fd9 0x7467627e3c318c7f

def z731 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff1c01fffc1e2f 0xabfffc7007fff078

def z732 : W := mkw 0xddfd0509df780000 0x2377f414277de000 0xffff9f8fffff1e3f 0xfffffe7e3ffffc78

def z733 : W := mkw 0xfdb6cf6c00000000 0x13f6db3db0000000 0xe1ff03fe00000008 0x1387fc0ff8000000

def z734 : W := mkw 0x6bfdf80175fad420 0x21aff7e005d7eb50 0x01fffc00007ffe18 0x4407fff00001fff8

def z735 : W := mkw 0xfdb6cf6c00000000 0x13f6db3db0000000 0xf9ff9ffe0000001d 0xf3e7fe7ff8000000

def z736 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f707f1ffffffe 0x9c18fdc1fc7fffff

def z737 : W := mkw 0xffb6ff6c8e000000 0x33fedbfdb2380000 0xfffffffe0c00001f 0xf3fffffff8300000

def z738 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x07ff03fe0000000e 0x901ffc0ff8000000

def z739 : W := mkw 0xffb6ff6c8a805420 0x13fedbfdb22a0150 0xfffffffe0380001f 0xf3fffffff80e0000

def z740 : W := mkw 0x2000c000aa82d420 0x0080030002aa0b50 0xf800fc01ff83fe37 0xefe003f007fe0ff8

def z741 : W := mkw 0xb400c000aa028000 0x02d0030002a80a00 0xfe00fc01ff83fe37 0xeff803f007fe0ff8

def z742 : W := mkw 0x020b383611ac7ce9 0x04082ce0d846b1f3 0x063f7c7e13fcfffe 0x9c18fdf1f84ff3ff

def z743 : W := mkw 0xd525058acb190b52 0x235494162b2c642d 0xe6279f8ee39f1fd2 0x5f989e7e3b8e7c7f

def z744 : W := mkw 0x9ed63dbd6057a19c 0x1a7b58f6f5815e86 0x1e1f1c0fe07fe1e4 0x2c787c703f81ff87

def z745 : W := mkw 0xddfd0003df780840 0x2377f4000f7de021 0xffff000ffffc01ef 0xbbfffc003ffff007

def z746 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xf800fc01ff83fe31 0x6fe003f007fe0ff8

def z747 : W := mkw 0xffb6ff6c20028000 0x13fedbfdb0800a00 0xfffffffee000e01f 0xfbfffffffb800380

def z748 : W := mkw 0xddfd0589df790312 0x2377f416277de40c 0xffff8f81ffff07ff 0xfffffe3e07fffc1f

def z749 : W := mkw 0xb602fa64aa82d420 0x12d80be992aa0b50 0xfe00fc71ff83fe37 0xeff803f1c7fe0ff8

def z750 : W := mkw 0x6bb6f76c00000000 0x11aedbddb0000000 0xe7fff3fe0000001f 0xd39fffcff8000000

def z751 : W := mkw 0xffb6ff6c2082d420 0x13fedbfdb0820b50 0xfffffffe1383fe3f 0xfffffffff84e0ff8

def z752 : W := mkw 0x6bb6ff6c2082d420 0x11aedbfdb0820b50 0x01fffffe0003fe18 0x5407fffff8000ff8

def z753 : W := mkw 0xddfd0083df790b52 0x2377f4020f7de42d 0xffff9c01ffff1fff 0xeffffe7007fffc7f

def z754 : W := mkw 0x0048008310610950 0x000120020c418425 0x19d89f8f1c631ffd 0xf467627e3c718c7f

def z755 : W := mkw 0x69b6c76c00000000 0x11a6db1db0000000 0xe1ff83fe00000009 0x5387fe0ff8000000

def z756 : W := mkw 0x49f9058b55790b52 0x0127e4162d55e42d 0xffff9f8fffff1fff 0xfffffe7e3ffffc7f

def z757 : W := mkw 0xd7603ad1cad575bc 0x0b5d80eb472b55d6 0x1fe01ff01ffc1fcc 0x307f807fc07ff07f

def z758 : W := mkw 0x69b8c75a7436aace 0x09a6e31d69d0daab 0xf8387c7efc1cfe06 0x2be0e1f1fbf073f8

def z759 : W := mkw 0x2202ff7e2086fce9 0x14880bfdf8821bf3 0x0000fffe0003ffd0 0x540003fff8000fff

def z760 : W := mkw 0x2202f7fe2087fbdf 0x0c880bdff8821fef 0x0000fffe0003ffd0 0x540003fff8000fff

def z761 : W := mkw 0x940900009b280000 0x02502400026ca000 0xe63f0000f3fc002e 0x8b98fc0003cff000

def z762 : W := mkw 0xbc9dc2d0bf2fa19c 0x2af2770b42fcbe86 0x1e1fe3f01f83e1d4 0x74787f8fc07e0f87

def z763 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff0000fffc000e 0x2bfffc0003fff000

def z764 : W := mkw 0x49fd07db557d2bde 0x2927f41f6d55f4af 0x01ff03fe007c01c8 0x1007fc0ff801f007

def z765 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0xe63f707ff3fcf9ff 0x9f98fdc1ffcff3e7

def z766 : W := mkw 0xddfd0749df780000 0x3377f41d277de000 0xffff0381fffc002f 0xabfffc0e07fff000

def z767 : W := mkw 0xbed8fd8bbee3df72 0x02fb63f62efb8f7d 0xe7d8638ee3e0e1ca 0x1b9f618e3b8f8387

def z768 : W := mkw 0x6bb2f76c00000000 0x01aecbddb0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z769 : W := mkw 0x0049009311ed79d9 0x040124024c47b5e7 0x0000000113fff9e0 0x0c000000044fffe7

def z770 : W := mkw 0xf726fa74ea96f4ac 0x1bdc9be9d3aa5bd2 0xe6276070e39ce002 0x0b989d81c38e7380

def z771 : W := mkw 0x0890058a00010b52 0x002240162800042d 0x19d89f8f1c031ffd 0xf467627e3c700c7f

def z772 : W := mkw 0x00490093dffd7bdb 0x240124024f7ff5ef 0x00000001ffffffe0 0x0c00000007ffffff

def z773 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xe7ff0001e3fc002b 0x8b9ffc00078ff000

def z774 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe009c01ff83fe25 0x6ff8027007fe0ff8

def z775 : W := mkw 0xddfd0003df780840 0x2377f4000f7de021 0xffff9c0fffff1fff 0xfffffe703ffffc7f

def z776 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff9c01fffc003f 0xebfffe7007fff000

def z777 : W := mkw 0xddfd0241df780000 0x2377f409077de000 0xffff03f1fffc002f 0xbbfffc0fc7fff000

def z778 : W := mkw 0xffb6ff6c8a000000 0x13fedbfdb2280000 0xffffffffec00001f 0xf3ffffffffb00000

def z779 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xf9e0e3f1fc7fe1ff 0xffe7838fc7f1ff87

def z780 : W := mkw 0x6bb6ff6c00000000 0x11aedbfdb0000000 0xe1fffffe0000001b 0xd387fffff8000000

def z781 : W := mkw 0xfdb6c76c00000000 0x13f6db1db0000000 0xffffe3fe0000001f 0xf3ffff8ff8000000

def z782 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x19ff1ffe0000000c 0x3067fc7ff8000000

def z783 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xfe279c01ff9f1e37 0xeff89e7007fe7c78

def z784 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xffc0ff81ff83fe3f 0xffff03fe07fe0ff8

def z785 : W := mkw 0xddfd0003df780a42 0x2377f4000f7de029 0xffff0001fffc1e2f 0xabfffc0007fff078

def z786 : W := mkw 0xddf40001ca500000 0x0377d00007294000 0xffff0001fffc002f 0xabfffc0007fff000

def z787 : W := mkw 0x4bb6376c00000000 0x112ed8ddb0000000 0x1ffffffe0000001f 0xf07ffffff8000000

def z788 : W := mkw 0x636bf2e771fbd955 0x0d8dafcb9dc7ef65 0xe7df938ff3831805 0x439f7e4e3fce0c60

def z789 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffff7ffe0000000e 0x33fffdfff8000000

def z790 : W := mkw 0xddfd0081df790110 0x2377f402077de404 0xffff0001ffff01ef 0xaffffc0007fffc07

def z791 : W := mkw 0xddb6076c00000000 0x1376d81db0000000 0x1fff03fe0000000c 0x307ffc0ff8000000

def z792 : W := mkw 0x9c9d00009f280000 0x22727400027ca000 0xfe3f0001fffc002f 0xabf8fc0007fff000

def z793 : W := mkw 0xffb6ff6c20028000 0x13fedbfdb0800a00 0xfffffffffc03fe3f 0xfffffffffff00ff8

def z794 : W := mkw 0xddfd050bdf780a42 0x2377f4142f7de029 0xffff000ffffc002f 0xabfffc003ffff000

def z795 : W := mkw 0xfdb4c74800000000 0x03f6d31d20000000 0xfffffffe0000001f 0xf3fffffff8000000

def z796 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff9f8ffffc01ff 0xfbfffe7e3ffff007

def z797 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0e3f0e07fe1da 0x5f87838fc381ff87

def z798 : W := mkw 0x9e963d2c00000000 0x127a58f4b0000000 0x1ffffffe0000001f 0xf07ffffff8000000

def z799 : W := mkw 0x2202fffc2087f5bc 0x18880bfff0821fd6 0x0000fffe0003ffd0 0x540003fff8000fff

def z800 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffffffff1c00003f 0xf3fffffffc700000

def z801 : W := mkw 0x0ad335bd05cd739b 0x042b4cd6f41735ce 0x1fe7eff10f9fe603 0x687f9fbfc43e7f98

def z802 : W := mkw 0xffb6ff6caa028420 0x13fedbfdb2a80a10 0xfffffffee000001f 0xf3fffffffb800000

def z803 : W := mkw 0xd56d0001df780000 0x2355b400077de000 0xe7e70001fffc002b 0x8b9f9c0007fff000

def z804 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xe7ff038ee3fc01ca 0x1b9ffc0e3b8ff007

def z805 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0xf9d89f8ffc631fff 0xffe7627e3ff18c7f

def z806 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xe6270001ff9c0022 0x0b989c0007fe7000

def z807 : W := mkw 0xbe92fd2c00000000 0x02fa4bf4b0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z808 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff8f8fffff07ef 0xfbfffe3e3ffffc1f

def z809 : W := mkw 0xb600fa40aa82d420 0x02d803e902aa0b50 0xfe00fff1ff83fe37 0xfff803ffc7fe0ff8

def z810 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe20fc71ff83fe3f 0xfff883f1c7fe0ff8

def z811 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f707e13fcf9ce 0x1818fdc1f84ff3e7

def z812 : W := mkw 0x00490093fffff9dd 0x2c0124024fffffe7 0x00000001fffff9e0 0x0c00000007ffffe7

def z813 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xe7ffe3fe0000001b 0xd39fff8ff8000000

def z814 : W := mkw 0x4bb6376c00000000 0x112ed8ddb0000000 0x07ff63fe0000000a 0x101ffd8ff8000000

def z815 : W := mkw 0x00090012112c28c8 0x000024004844b0a3 0x063f707e13fcf9fe 0x9c18fdc1f84ff3e7

def z816 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffe70001fffc0023 0x2bff9c0007fff000

def z817 : W := mkw 0x0202303400847088 0x000808c0d00211c2 0x063f707e13fcf9fe 0x9c18fdc1f84ff3e7

def z818 : W := mkw 0xddf50001cf580000 0x2377d400073d6000 0xffff0001ef9c000f 0xabfffc0007be7000

def z819 : W := mkw 0xddbd0000df380000 0x2376f400037ce000 0xfe3f0000fffc002e 0xabf8fc0003fff000

def z820 : W := mkw 0xd56d0001db780000 0x2355b400076de000 0xe7ff0001f3fc002f 0x8b9ffc0007cff000

def z821 : W := mkw 0xddfd050bdf780a42 0x2377f4142f7de029 0xffff9c0fffff1e3f 0xeffffe703ffffc78

def z822 : W := mkw 0x940100008b080000 0x02500400022c2000 0xe6270000e39c0002 0x0b989c00038e7000

def z823 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe00fc01ffe3ffff 0xfff803f007ff8fff

def z824 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff6001fffce03f 0xaffffd8007fff380

def z825 : W := mkw 0xffb6ff6c00805000 0x13fedbfdb0020140 0xfffffffe1380181f 0xf3fffffff84e0060

def z826 : W := mkw 0xddfd0081df790110 0x2377f402077de404 0xffff0381fffc01ef 0xbbfffc0e07fff007

def z827 : W := mkw 0xd5650001cb580000 0x23559400072d6000 0xffe70001fffc002f 0xabff9c0007fff000

def z828 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d89f8e1c631fdc 0x7467627e38718c7f

def z829 : W := mkw 0x2040c0912047a198 0x0081030244811e86 0xe1e0e3f1e07fe1fb 0xdf87838fc781ff87

def z830 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f707e03fcf9da 0x1c18fdc1f80ff3e7

def z831 : W := mkw 0xddb50000cb180000 0x2376d400032c6000 0xffff0001ff9c002f 0xabfffc0007fe7000

def z832 : W := mkw 0xddfd02c1df790114 0x2b77f40b077de404 0xffff0381fffc002f 0xabfffc0e07fff000

def z833 : W := mkw 0x0249309315ed7bdb 0x040924c24c57b5ef 0x1e00fc011ffffff7 0xec7803f0047fffff

def z834 : W := mkw 0x0898050a10200840 0x0022601428408021 0x19d89f8f1c631ffd 0xf467627e3c718c7f

def z835 : W := mkw 0xffb6ff6c8a805420 0x13fedbfdb22a0150 0xfffffffe1f80fe3f 0xfffffffff87e03f8

def z836 : W := mkw 0xddb50000cb180000 0x2376d400032c6000 0xe7ff0000e39c000a 0x0b9ffc00038e7000

def z837 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe0000e03f 0xfffffffff8000380

def z838 : W := mkw 0xfdb6cf6c00000000 0x13f6db3db0000000 0xffff8ffe0000000f 0xf3fffe3ff8000000

def z839 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0e3f1e07fe1cb 0x5b87838fc781ff87

def z840 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff1001fffc183f 0xaffffc4007fff060

def z841 : W := mkw 0xffb6ff6caa028420 0x13fedbfdb2a80a10 0xfffffffffc031e3f 0xf7fffffffff00c78

def z842 : W := mkw 0xb649f893fbfffdfd 0x0ed927e24feffff7 0xfe00fc01fffffff7 0xeff803f007ffffff

def z843 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe00031e1f 0xf7fffffff8000c78

def z844 : W := mkw 0xddb6076c00000000 0x1376d81db0000000 0xffff9ffe0000001f 0xf3fffe7ff8000000

def z845 : W := mkw 0x0049009351fd79dd 0x0c0124024d47f5e7 0x0000000013fcf9e0 0x0c000000004ff3e7

def z846 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe00000007 0x63fffffff8000000

def z847 : W := mkw 0xddb50000cf180000 0x2376d400033c6000 0xfe270000ef9c0002 0x2bf89c0003be7000

def z848 : W := mkw 0xd5650001cb580000 0x23559400072d6000 0xe7e70001e39c0003 0x0b9f9c00078e7000

def z849 : W := mkw 0xd52d0000db380000 0x2354b400036ce000 0xe6270000f3fc0022 0x0b989c0003cff000

def z850 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xe63f0000e39c000e 0x8b98fc00038e7000

def z851 : W := mkw 0xd56d0083df790b52 0x2355b4020f7de42d 0xe6270001ffff1fe2 0x0f989c0007fffc7f

def z852 : W := mkw 0xffb6ff6c8a000000 0x13fedbfdb2280000 0xfffffffe1f80001f 0xf3fffffff87e0000

def z853 : W := mkw 0x49f9000155780000 0x0127e4000555e000 0xffff0001fffc002f 0xabfffc0007fff000

def z854 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff138ffffc19ff 0xbffffc4e3ffff067

def z855 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x1fff9f8f1c631fff 0xf47ffe7e3c718c7f

def z856 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff0001ffff1e2f 0xaffffc0007fffc78

def z857 : W := mkw 0xddfd0081df790110 0x2377f402077de404 0xffff9f81ffff1fff 0xfffffe7e07fffc7f

def z858 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0xe1ff03fe0000000b 0x9387fc0ff8000000

def z859 : W := mkw 0x4bb6376c00000000 0x112ed8ddb0000000 0x07ff13fe0000000c 0x101ffc4ff8000000

def z860 : W := mkw 0x9cd9058b9f690b52 0x027364162e7da42d 0xffff9f8fffff1fff 0xfffffe7e3ffffc7f

def z861 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xffffffffec03fe1f 0xf7ffffffffb00ff8

def z862 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xe7ff63fee380e00a 0x1b9ffd8ffb8e0380

def z863 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f707e13fcf9dc 0x1418fdc1f84ff3e7

def z864 : W := mkw 0xddfd050bdf780a42 0x2377f4142f7de029 0xffff9f8ffffc1e3f 0xfbfffe7e3ffff078

def z865 : W := mkw 0xdff63037ced478c9 0x277fd8c0df3b51e3 0xf9c0707fec00f9d1 0x37e701c1ffb003e7

def z866 : W := mkw 0x4160009140552198 0x0105800245015486 0xe1e0e3f1e07fe1fb 0xdf87838fc781ff87

def z867 : W := mkw 0xddb50508cb180000 0x2376d414232c6000 0xffff9f8ee39c001f 0xfbfffe7e3b8e7000

def z868 : W := mkw 0xddfd0589df790110 0x2377f416277de404 0xffff9f8fffff01ff 0xfffffe7e3ffffc07

def z869 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1f8f3ffe07fe1ff 0xdf87e3cfff81ff87

def z870 : W := mkw 0x4129000051380000 0x0104a4000144e000 0xe63f0000f3fc002e 0x8b98fc0003cff000

def z871 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe00fc01ff83fe07 0x6bf803f007fe0ff8

def z872 : W := mkw 0x2202f2742086f08d 0x0c880bc9d0821bc2 0x000060700000e000 0x00000181c0000380

def z873 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f607e13fcf9ea 0x1c18fd81f84ff3e7

def z874 : W := mkw 0x6bb6ff6c00000000 0x11aedbfdb0000000 0x01ff63fe00000008 0x1007fd8ff8000000

def z875 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xfffffffef380f83f 0xfffffffffbce03e0

def z876 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x1e3f7c7e1ffcfffe 0xbc78fdf1f87ff3ff

def z877 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff0000e3fc000f 0xabfffc00038ff000

def z878 : W := mkw 0xdfb63f6c8a805420 0x137ed8fdb22a0150 0x1fff1ffe1f801e0c 0x307ffc7ff87e0078

def z879 : W := mkw 0xddb50000cb180000 0x2376d400032c6000 0xfe3f0000e39c0006 0x2bf8fc00038e7000

def z880 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff6071fffc003f 0xbbfffd81c7fff000

def z881 : W := mkw 0xddfd0d09df780000 0x3377f434277de000 0xffff0c01fffc002f 0xabfffc3007fff000

def z882 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xfffffffeff80fe1f 0xfbfffffffbfe03f8

def z883 : W := mkw 0x2200f0002082d000 0x008803c000820b40 0xfe00fc01ff83fe37 0xeff803f007fe0ff8

def z884 : W := mkw 0xddfd0589df790312 0x2377f416277de40c 0xffff0381fffc002f 0xabfffc0e07fff000

def z885 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe20fc01fffffe3f 0xeff883f007fffff8

def z886 : W := mkw 0xffb6ff6c00805420 0x13fedbfdb0020150 0xfffffffe00001e1f 0xf3fffffff8000078

def z887 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff038fffff1fef 0xbffffc0e3ffffc7f

def z888 : W := mkw 0x2202f0362086f8c9 0x04880bc0d8821be3 0x0000f07e0003f9d0 0x540003c1f8000fe7

def z889 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x19ff03fe0000000d 0xb067fc0ff8000000

def z890 : W := mkw 0x00490093156d2bdb 0x040124024c55b4af 0x00000000007c01c0 0x000000000001f007

def z891 : W := mkw 0x2202f2762086f8cd 0x0c880bc9d8821be3 0x0000707e0000f9d0 0x140001c1f80003e7

def z892 : W := mkw 0xffb6ff6cca100000 0x33fedbfdb3284000 0xfffffffee000001f 0xf3fffffffb800000

def z893 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe007c003f 0xfbfffffff801f000

def z894 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e063f0e07ce1fa 0x9f87818fc381f387

def z895 : W := mkw 0x6120c2502006a088 0x0184830940801a82 0xe1e0e3f1e07fe1fb 0xdf87838fc781ff87

def z896 : W := mkw 0xffb6ff6caa028420 0x13fedbfdb2a80a10 0xffffffffff83063f 0xfbfffffffffe0c18

def z897 : W := mkw 0xfdf4c7c9ee538316 0x2bf7d31f27b94e0c 0xf9c08f81ec030601 0x63e7023e07b00c18

def z898 : W := mkw 0x4322326400000000 0x010c88c990000000 0x07ff73fe0000001e 0x901ffdcff8000000

def z899 : W := mkw 0xb649f893bfeffffb 0x06d927e24effbfff 0xfe00fc01fffffff7 0xeff803f007ffffff

def z900 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x01ff63fe0000001a 0x9007fd8ff8000000

def z901 : W := mkw 0x9e9f3d2e9ba85c61 0x167a7cf4ba6ea171 0x1e1f1c0e1f801e04 0x20787c70387e0078

def z902 : W := mkw 0x4bb6376c00805000 0x112ed8ddb0020140 0x07ff73fe1380f83e 0x9c1ffdcff84e03e0

def z903 : W := mkw 0x960030008a805000 0x025800c0022a0140 0xfe00fc01ff83fe37 0xeff803f007fe0ff8

def z904 : W := mkw 0xdfb63f6c00000000 0x137ed8fdb0000000 0x1fff7ffe0000001e 0xb07ffdfff8000000

def z905 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xffffffffe383e03f 0xffffffffff8e0f80

def z906 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063ffc7e13fffffe 0xdc18fff1f84fffff

def z907 : W := mkw 0x0a92352c00000000 0x002a48d4b0000000 0x07ff73fe0000001e 0x901ffdcff8000000

def z908 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xfe270000ff9c0006 0x2bf89c0003fe7000

def z909 : W := mkw 0xddfd0509df780000 0x2377f414277de000 0xffff038ffffc002f 0xbbfffc0e3ffff000

def z910 : W := mkw 0x08d9058b55790b52 0x202364162d55e42d 0x19d89f8f1c7f1ffd 0xf467627e3c71fc7f

def z911 : W := mkw 0xddfd0003df780840 0x2377f4000f7de021 0xffff100ffffc182f 0xabfffc403ffff060

def z912 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xffffffffef83e61f 0xfbffffffffbe0f98

def z913 : W := mkw 0x49fd000155780000 0x2127f4000555e000 0xe7ff0001f3fc002f 0x8b9ffc0007cff000

def z914 : W := mkw 0xffb6ff6c8a000420 0x13fedbfdb2280010 0xfffffffe0c00061f 0xf3fffffff8300018

def z915 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe7e0e3f1f3ffe1ff 0xdf9f838fc7cfff87

def z916 : W := mkw 0x9cdd0001df780000 0x22737400077de000 0xfe1f0001fffc0027 0xabf87c0007fff000

def z917 : W := mkw 0xddfd0589df790312 0x2377f416277de40c 0xffff9f81ffff1e3f 0xeffffe7e07fffc78

def z918 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19f89f8f1c7f1fff 0xfc67e27e3c71fc7f

def z919 : W := mkw 0x224af2f730e7f9dd 0x0c892bcbdcc39fe7 0x01d8f3ff1063f9fd 0xd40763cffc418fe7

def z920 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xe6270001e39c0023 0x8b989c00078e7000

def z921 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0x1ffffffe0000001c 0x707ffffff8000000

def z922 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff0001fffc000d 0x23fffc0007fff000

def z923 : W := mkw 0x69b6c76c00000000 0x11a6db1db0000000 0x01ffe3fe00000018 0x5007ff8ff8000000

def z924 : W := mkw 0x69b6c76c00000000 0x11a6db1db0000000 0xf9fffffe0000001f 0xf3e7fffff8000000

def z925 : W := mkw 0x6160cad16057a5bc 0x0985832b45815e96 0xe1e0eff1e07fe7fb 0xdf8783bfc781ff9f

def z926 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff8c01ffff062f 0xebfffe3007fffc18

def z927 : W := mkw 0x0040058b00410b52 0x000100162c01042d 0x19c09f8f1c631ffd 0xf467027e3c718c7f

def z928 : W := mkw 0xddfd0083df790b52 0x2377f4020f7de42d 0xffff100fffff1fff 0xbffffc403ffffc7f

def z929 : W := mkw 0xfdb6cf6c00000000 0x13f6db3db0000000 0xf9ffeffe0000001b 0xf3e7ffbff8000000

def z930 : W := mkw 0x08dd058b15690b52 0x202374162c55a42d 0x19df9f8f1c631ffd 0xf4677e7e3c718c7f

def z931 : W := mkw 0xd56d0001df780000 0x2355b400077de000 0xe6270000e3fc0002 0x0b989c00038ff000

def z932 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d89f8f1c031fd5 0x7467627e3c700c7f

def z933 : W := mkw 0x4122026400000000 0x0104880990000000 0x01ff03fe00000008 0x1007fc0ff8000000

def z934 : W := mkw 0x940900029b280840 0x025024000a6ca021 0xfe3f9c0fffff1fff 0xfff8fe703ffffc7f

def z935 : W := mkw 0xffb6ff6c8a000000 0x13fedbfdb2280000 0xffffffffff831e3f 0xfffffffffffe0c78

def z936 : W := mkw 0xf723fa74eb9ef4ad 0x0fdc8fe9d3ae7bd2 0xe6276070e39ce002 0x0b989d81c38e7380

def z937 : W := mkw 0x00490093ff7fabde 0x280124024ffdfeaf 0x00000001ffffffe0 0x0c00000007ffffff

def z938 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e063f1e07ce1eb 0x9b87818fc781f387

def z939 : W := mkw 0x2202f2f42087f19d 0x0c880bcbd0821fc6 0x0000e3f00003e1d0 0x5400038fc0000f87

def z940 : W := mkw 0xddfd0081df790312 0x2377f402077de40c 0xffff0001ffff062f 0xabfffc0007fffc18

def z941 : W := mkw 0x2adaf7ff34e7fbdf 0x0cab6bdffcd39fef 0x19d8ffff1c63fffd 0xf46763fffc718fff

def z942 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x07fff3fe13fcf9ff 0xdc1fffcff84ff3e7

def z943 : W := mkw 0x0a92352c00805000 0x002a48d4b0020140 0x1fffffff1f83fe3f 0xfc7ffffffc7e0ff8

def z944 : W := mkw 0x416002d14055219c 0x0905800b45015486 0xe1e063f1e07ce1fb 0x9f87818fc781f387

def z945 : W := mkw 0xffb6ff6c2082d420 0x13fedbfdb0820b50 0xffffffff1c03fe3f 0xf7fffffffc700ff8

def z946 : W := mkw 0xffb6ff6c04000202 0x13fedbfdb0100008 0xfffffffe0c00061f 0xf3fffffff8300018

def z947 : W := mkw 0x2202faf62087fdfd 0x0c880bebd8821ff7 0x0000fffe0003ffd0 0x540003fff8000fff

def z948 : W := mkw 0xffb6ff6c8a000000 0x13fedbfdb2280000 0xfffffffee380001f 0xfbfffffffb8e0000

def z949 : W := mkw 0xffb6ff6c8a805420 0x13fedbfdb22a0150 0xffffffffff801e3f 0xfbfffffffffe0078

def z950 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff0001effc000b 0x2bfffc0007bff000

def z951 : W := mkw 0x0049009375fffbdf 0x0c0124024dd7ffef 0x00000001ffffffe0 0x0c00000007ffffff

def z952 : W := mkw 0xdfb6352c00000000 0x037ed8d4b0000000 0xfffffffe0000001f 0xf3fffffff8000000

def z953 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x19ff8ffe00000009 0x7067fe3ff8000000

def z954 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffffffffe000003f 0xfbffffffff800000

def z955 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffff9ffe0000000d 0x73fffe7ff8000000

def z956 : W := mkw 0x9e9f352e9fa85a43 0x267a7cd4ba7ea169 0x1e1f1c0e1f801e04 0x20787c70387e0078

def z957 : W := mkw 0xb400c800aa82d420 0x02d0032002aa0b50 0xf800ec01ff83fe33 0xefe003b007fe0ff8

def z958 : W := mkw 0x6322ff6c00000000 0x118c8bfdb0000000 0xe7fffffe0000001f 0xd39ffffff8000000

def z959 : W := mkw 0xf722fa64aa82d420 0x03dc8be992aa0b50 0xffffffffff83fe3f 0xfffffffffffe0ff8

def z960 : W := mkw 0x020b3034112c2088 0x00082cc0d044b082 0x063f707e13fce1fe 0x9c18fdc1f84ff387

def z961 : W := mkw 0x00490093fbfffdfd 0x0c0124024feffff7 0x00000001ffffffe0 0x0c00000007ffffff

def z962 : W := mkw 0xffb6ff6c2082d420 0x13fedbfdb0820b50 0xfffffffe0000e01f 0xf3fffffff8000380

def z963 : W := mkw 0x94490001df780000 0x22512400077de000 0xfe3f0001fffc002f 0xabf8fc0007fff000

def z964 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff9f8fffff1e2f 0xebfffe7e3ffffc78

def z965 : W := mkw 0xddfd050bdf780a42 0x2377f4142f7de029 0xffff1c0ffffc1fff 0xbffffc703ffff07f

def z966 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe007c01ff83fe26 0x2ff801f007fe0ff8

def z967 : W := mkw 0xddbd00009b280000 0x0376f400026ca000 0xffff0001fffc002f 0xabfffc0007fff000

def z968 : W := mkw 0xddbd050adf380a42 0x2376f4142b7ce029 0xfe3f1c0eff9c1e06 0x2bf8fc703bfe7078

def z969 : W := mkw 0x49fb07ff557d2bdf 0x0d27ec1ffd55f4af 0x01ff03fe007c01c8 0x1007fc0ff801f007

def z970 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xe7e70000e39c000b 0x8b9f9c00038e7000

def z971 : W := mkw 0x00490093156d2bdb 0x040124024c55b4af 0x000000011c7f1fe0 0x040000000471fc7f

def z972 : W := mkw 0x6bb6ff6c00000000 0x11aedbfdb0000000 0x07fffffe0000001e 0xd01ffffff8000000

def z973 : W := mkw 0xddbd0000df380000 0x2376f400037ce000 0xe63f0000e39c0002 0x0b98fc00038e7000

def z974 : W := mkw 0x69b6cf6c00000000 0x11a6db3db0000000 0x01ff8ffe00000008 0x5007fe3ff8000000

def z975 : W := mkw 0x0892052c00000000 0x00224814b0000000 0x01ff03fe00000008 0x1007fc0ff8000000

def z976 : W := mkw 0xddfd0509df780202 0x2377f414277de008 0xffff0c01fffc062f 0xabfffc3007fff018

def z977 : W := mkw 0xddf50001cf580000 0x2377d400073d6000 0xe7e70000e39c0002 0x0b9f9c00038e7000

def z978 : W := mkw 0x2a92ff6c00000000 0x10aa4bfdb0000000 0x1ffffffe0000001f 0xf07ffffff8000000

def z979 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff0001ff9c0007 0x2bfffc0007fe7000

def z980 : W := mkw 0xddb50000cb180000 0x2376d400032c6000 0xffe70000e39c0003 0x2bff9c00038e7000

def z981 : W := mkw 0x2249f09371fff9dd 0x0c8927c24dc7ffe7 0xe600f001f3fff9f7 0xcf9803c007cfffe7

def z982 : W := mkw 0x020b303615ac7acb 0x04082cc0d856b1eb 0x063f707e1ffcfffe 0x9c18fdc1f87ff3ff

def z983 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe1000183f 0xf7fffffff8400060

def z984 : W := mkw 0xb400c800aa82d420 0x02d0032002aa0b50 0xfe008c01ff83fe27 0xeff8023007fe0ff8

def z985 : W := mkw 0xd52d0000db380000 0x2354b400036ce000 0xe63f0000e3fc000a 0x0b98fc00038ff000

def z986 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0fff1e07ffffb 0xdf8783ffc781ffff

def z987 : W := mkw 0xbe92fd2caa82d420 0x02fa4bf4b2aa0b50 0xffffffffff83fe3f 0xfffffffffffe0ff8

def z988 : W := mkw 0x6160c25140542088 0x0185830945015082 0xe1e0e3f1e07ce1fb 0xdf87838fc781f387

def z989 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe1c001e1f 0xf3fffffff8700078

def z990 : W := mkw 0xfdb6cf6caa028420 0x13f6db3db2a80a10 0xf9ff8fffec030609 0x73e7fe3fffb00c18

def z991 : W := mkw 0x6120c2506016a08c 0x0984830941805a82 0xe1e0e3f0e07ce1fb 0xdf87838fc381f387

def z992 : W := mkw 0x08d0058b04410b52 0x002340162c11042d 0x19c09f8f0c631ff9 0xf467027e3c318c7f

def z993 : W := mkw 0xd5650001cb580000 0x23559400072d6000 0xe7e70000e3fc000a 0x0b9f9c00038ff000

def z994 : W := mkw 0x9cd900019f680000 0x02736400067da000 0xffff0001fffc002f 0xabfffc0007fff000

def z995 : W := mkw 0x2202fdbe2087fffb 0x04880bf6f8821fff 0x0000fffe0003ffd0 0x540003fff8000fff

def z996 : W := mkw 0x41690001df780000 0x2105a400077de000 0xe7ff0001fffc002f 0x8b9ffc0007fff000

def z997 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe7ffe3f1e07fe1ff 0xdf9fff8fc781ff87

def z998 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x1e3f707f1ffcf9ff 0xbc78fdc1fc7ff3e7

def z999 : W := mkw 0x9e9f3d2e9fa85841 0x367a7cf4ba7ea161 0x1e1f1c0e1f801804 0x20787c70387e0060

def z1000 : W := mkw 0xd52d0000df380000 0x2354b400037ce000 0xe6270000ff9c0002 0x0b989c0003fe7000

def z1001 : W := mkw 0xd52d0002db380840 0x2354b4000b6ce021 0xe63f100ef3fc19fe 0x9f98fc403bcff067

def z1002 : W := mkw 0xb602f824aa82d420 0x02d80be092aa0b50 0xfe27fc71ff83fe37 0xeff89ff1c7fe0ff8

def z1003 : W := mkw 0x0898058a14210b52 0x002260162850842d 0x19d89f8e1c031fdd 0xf467627e38700c7f

def z1004 : W := mkw 0x6322f2642082d000 0x018c8bc990820b40 0xe7fff3fff383f83f 0xdf9fffcfffce0fe0

def z1005 : W := mkw 0x08d9058b15690b52 0x002364162c55a42d 0x19ff9f8f1c7f1ffd 0xf467fe7e3c71fc7f

def z1006 : W := mkw 0xdfb6376c00000000 0x137ed8ddb0000000 0xffff73fe0000001f 0xb3fffdcff8000000

def z1007 : W := mkw 0xb602f824aa82d420 0x02d80be092aa0b50 0xfe00fc7fff83fe37 0xfff803f1fffe0ff8

def z1008 : W := mkw 0xddfd0589df790312 0x2377f416277de40c 0xffff9f8fffff063f 0xfbfffe7e3ffffc18

def z1009 : W := mkw 0x6160c2d16457a39e 0x0985830b45915e8e 0xe1e0e3f1ec7fe7fb 0xdf87838fc7b1ff9f

def z1010 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x01ff9ffe00000018 0x5007fe7ff8000000

def z1011 : W := mkw 0x96003800aa82d420 0x025800e002aa0b50 0xfe001c01ff83fe27 0xaff8007007fe0ff8

def z1012 : W := mkw 0xd52d0000db380000 0x2354b400036ce000 0xe63f0000f39c0006 0x0b98fc0003ce7000

def z1013 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffffeffe0000000b 0x73ffffbff8000000

def z1014 : W := mkw 0x0049009315ed7bdb 0x040124024c57b5ef 0x0000000013fcf9e0 0x0c000000004ff3e7

def z1015 : W := mkw 0x49ff05bf557d2bdb 0x2527fc16fd55f4af 0x01ff03fe007c01c8 0x1007fc0ff801f007

def z1016 : W := mkw 0x2202f8342086f4a9 0x04880be0d0821bd2 0x0000fc700003fe10 0x440003f1c0000ff8

def z1017 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063ff07f13fff9ff 0xdc18ffc1fc4fffe7

def z1018 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe1380003f 0xfbfffffff84e0000

def z1019 : W := mkw 0x08d8058b54710b52 0x002360162d51c42d 0x19d89f8ffc7f1ffd 0xfc67627e3ff1fc7f

def z1020 : W := mkw 0xb602f824aa82d420 0x02d80be092aa0b50 0xfe1ffc0fff83fe37 0xeff87ff03ffe0ff8

def z1021 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff8001ffff003f 0xeffffe0007fffc00

def z1022 : W := mkw 0xffb6ff6c2082d420 0x13fedbfdb0820b50 0xffffffffe003fe3f 0xffffffffff800ff8

def z1023 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe00fc01ff83fe15 0x67f803f007fe0ff8

def z1024 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xf9fffffe00000019 0x73e7fffff8000000

def z1025 : W := mkw 0x02033034018c7089 0x04080cc0d00631c2 0x063f707e03fce1fe 0x9c18fdc1f80ff387

def z1026 : W := mkw 0xbe96ff6c00000000 0x12fa5bfdb0000000 0x1fdffffe0000001d 0xf07f7ffff8000000

def z1027 : W := mkw 0xd5690001db780000 0x0355a400076de000 0xffff0001fffc002f 0xabfffc0007fff000

def z1028 : W := mkw 0xddfd0083df790b52 0x2377f4020f7de42d 0xffff8381ffff1fff 0xfffffe0e07fffc7f

def z1029 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xffffffffff831e1f 0xf3fffffffffe0c78

def z1030 : W := mkw 0xffb6ff6c40100000 0x13fedbfdb1004000 0xfffffffee01c001f 0xfbfffffffb807000

def z1031 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff838fffff01ff 0xfffffe0e3ffffc07

def z1032 : W := mkw 0xffb6ff6c20028000 0x13fedbfdb0800a00 0xffffffffe003001f 0xf3ffffffff800c00

def z1033 : W := mkw 0xfdf4cfc9ee538114 0x3bf7d33f27b94e04 0xf9c08f81ec030001 0x63e7023e07b00c00

def z1034 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19f8ffff1c631fff 0xf467e3fffc718c7f

def z1035 : W := mkw 0x6122c26400000000 0x01848b0990000000 0xe1ffe3fe0000001b 0xd387ff8ff8000000

def z1036 : W := mkw 0x0892052c00000000 0x00224814b0000000 0x19ff9ffe0000001d 0xf067fe7ff8000000

def z1037 : W := mkw 0xd5650001cb580000 0x23559400072d6000 0xe6270001e3fc0022 0x0b989c00078ff000

def z1038 : W := mkw 0xddfd000151780000 0x0377f4000545e000 0xffff0001f3fc002f 0xabfffc0007cff000

def z1039 : W := mkw 0xdfb63f6c00000000 0x137ed8fdb0000000 0x07ff03fe00000008 0x101ffc0ff8000000

def z1040 : W := mkw 0x94000000aa82d420 0x0250000002aa0b50 0xfe009c01ff83fe37 0xeff8027007fe0ff8

def z1041 : W := mkw 0xdfb63f6c00000000 0x137ed8fdb0000000 0x1fff9ffe0000001d 0xf07ffe7ff8000000

def z1042 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xfffffffe1f83fe1f 0xf7fffffff87e0ff8

def z1043 : W := mkw 0xffb6ff6c20028000 0x13fedbfdb0800a00 0xfffffffe0003e01f 0xf7fffffff8000f80

def z1044 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff1c0fffff1fef 0xaffffc703ffffc7f

def z1045 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xe7ff73fe0000001e 0x939ffdcff8000000

def z1046 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x01ff13fe0000001c 0x9007fc4ff8000000

def z1047 : W := mkw 0x69b6c76c00000000 0x11a6db1db0000000 0xe1ff63fe0000000a 0x1387fd8ff8000000

def z1048 : W := mkw 0xdfb63f6c00000000 0x137ed8fdb0000000 0xffff1ffe0000000f 0xb3fffc7ff8000000

def z1049 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xe7ff0000f3fc002e 0x8b9ffc0003cff000

def z1050 : W := mkw 0xddf50589cf590312 0x2377d416273d640c 0xffe78f81ef9f0603 0x6bff9e3e07be7c18

def z1051 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff100ffffc003f 0xbbfffc403ffff000

def z1052 : W := mkw 0xddbd0000db380000 0x2376f400036ce000 0xffff0000f3fc002f 0xabfffc0003cff000

def z1053 : W := mkw 0xd5650001cf580000 0x23559400073d6000 0xe6270001ef9c0002 0x0b989c0007be7000

def z1054 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0e3f0e07ce1db 0xdb87838fc381f387

def z1055 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x1fd89f8f1fe31fff 0xfc7f627e3c7f8c7f

def z1056 : W := mkw 0xffb6ff6c00805000 0x13fedbfdb0020140 0xffffffff1f83fe3f 0xfffffffffc7e0ff8

def z1057 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe00ec01ff83fe23 0x6ff803b007fe0ff8

def z1058 : W := mkw 0x940100008b080000 0x02500400022c2000 0xfe270001ff9c0027 0xabf89c0007fe7000

def z1059 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xfffffffee383fe1f 0xfffffffffb8e0ff8

def z1060 : W := mkw 0xddfd0509df780000 0x2377f414277de000 0xffff1c0ffffc002f 0xabfffc703ffff000

def z1061 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffdf0001fffc0025 0x2bff7c0007fff000

def z1062 : W := mkw 0xddb60f6c00000000 0x1376d83db0000000 0x19ff0ffe00000008 0x3067fc3ff8000000

def z1063 : W := mkw 0xddfd0801df780420 0x2377f420077de010 0xffff0c01fffc062f 0xabfffc3007fff018

def z1064 : W := mkw 0xddbd0000df380000 0x2376f400037ce000 0xffff0000ff9c000f 0xabfffc0003fe7000

def z1065 : W := mkw 0x2202f8342086f4a9 0x04880be0d0821bd2 0x000060700000e000 0x00000181c0000380

def z1066 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffff63fe0000000f 0xb3fffd8ff8000000

def z1067 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff1f8ffffc1fef 0xbbfffc7e3ffff07f

def z1068 : W := mkw 0xddb6076c00000000 0x1376d81db0000000 0xe7ff03fe0000000a 0x139ffc0ff8000000

def z1069 : W := mkw 0xb606f824aa82d420 0x12d81be092aa0b50 0xfe07fc01ff83fe37 0xeff81ff007fe0ff8

def z1070 : W := mkw 0xddb6076c8a000000 0x1376d81db2280000 0xffff03ffff80002f 0xbbfffc0ffffe0000

def z1071 : W := mkw 0x08d9058b15690b52 0x002364162c55a42d 0x19d89f8f1fff1ffd 0xfc67627e3c7ffc7f

def z1072 : W := mkw 0xd5650081cb590110 0x23559402072d6404 0xe7e78381e3ff01fb 0xdf9f9e0e078ffc07

def z1073 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0e3f1e07fe1e3 0x4f87838fc781ff87

def z1074 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x01ff83fe00000019 0xd007fe0ff8000000

def z1075 : W := mkw 0xf726fa6400000000 0x13dc9be990000000 0xe7fff3fe0000001f 0xd39fffcff8000000

def z1076 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xf9e0fff1e07fe1ff 0xffe783ffc781ff87

def z1077 : W := mkw 0x08d8058b14610b52 0x002360162c51842d 0x19d8ff8f1c63ffff 0xfc6763fe3c718fff

def z1078 : W := mkw 0xffb6ff6c2082d000 0x13fedbfdb0820b40 0xfffffffff383f83f 0xffffffffffce0fe0

def z1079 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xe7fffffe0000001a 0x539ffffff8000000

def z1080 : W := mkw 0xffb6ff6c60128004 0x1bfedbfdb1804a00 0xfffffffee000001f 0xf3fffffffb800000

def z1081 : W := mkw 0x2202f8362086fce9 0x04880be0d8821bf3 0x0000707e0000f9d0 0x140001c1f80003e7

def z1082 : W := mkw 0x69b6c76c20028000 0x11a6db1db0800a00 0xe1ffe3ffe003e03b 0xdf87ff8fff800f80

def z1083 : W := mkw 0x000b0036112c28c9 0x04002c00d844b0a3 0x063f607e13fce1fe 0x9c18fd81f84ff387

def z1084 : W := mkw 0x4bb63f6c00000000 0x112ed8fdb0000000 0x01ff1ffe00000008 0x1007fc7ff8000000

def z1085 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0f3f1f07ff9ff 0xdf8783cfc7c1ffe7

def z1086 : W := mkw 0xddfd0003df780840 0x2377f4000f7de021 0xffff0001fffc19ef 0xaffffc0007fff067

def z1087 : W := mkw 0xffb6ff6c00805000 0x13fedbfdb0020140 0xfffffffe0000f81f 0xf7fffffff80003e0

def z1088 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f707e03fce1de 0x9818fdc1f80ff387

def z1089 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xfe270000e39c0007 0xabf89c00038e7000

def z1090 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffdffffe00000015 0x73ff7ffff8000000

def z1091 : W := mkw 0xb400c800aa82d420 0x02d0032002aa0b50 0xf8009c01ff83fe35 0xefe0027007fe0ff8

def z1092 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xf9e0eff1ec7fe7fb 0xffe783bfc7b1ff9f

def z1093 : W := mkw 0x00490093bfeffffb 0x040124024effbfff 0x00000001ffffffe0 0x0c00000007ffffff

def z1094 : W := mkw 0xddb6076c00000000 0x1376d81db0000000 0xf9ff03fe00000009 0x33e7fc0ff8000000

def z1095 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e063f1e07fe1ea 0x1f87818fc781ff87

def z1096 : W := mkw 0xddf50001cf580000 0x2377d400073d6000 0xffe70001effc002b 0xabff9c0007bff000

def z1097 : W := mkw 0xffb6ff6c8a805420 0x13fedbfdb22a0150 0xffffffff1f831e3f 0xf7fffffffc7e0c78

def z1098 : W := mkw 0xffb6ff6caa028000 0x13fedbfdb2a80a00 0xffffffffff83e03f 0xfffffffffffe0f80

def z1099 : W := mkw 0x4bb6376c00000000 0x112ed8ddb0000000 0x01ff73fe00000018 0x1007fdcff8000000

def z1100 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffffffff0003003f 0xf7fffffffc000c00

def z1101 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0e3f1fc7ffffb 0xdf87838fc7f1ffff

def z1102 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xffffffff0c03061f 0xf3fffffffc300c18

def z1103 : W := mkw 0x0202302400000000 0x000808c090000000 0x07fff3fe0000001f 0xd01fffcff8000000

def z1104 : W := mkw 0x6160c2d16057a19c 0x0985830b45815e86 0xe1e0e3f1e07fe1d9 0x5787838fc781ff87

def z1105 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f707e13fcf9e6 0x0c18fdc1f84ff3e7

def z1106 : W := mkw 0xffb6ff6c00000000 0x13fedbfdb0000000 0xfffffffe006001ff 0xf7fffffff8018007

def z1107 : W := mkw 0xddfd0083df790950 0x2377f4020f7de425 0xffff938fffff19ff 0xfffffe4e3ffffc67

def z1108 : W := mkw 0xddf50001cb580000 0x2377d400072d6000 0xffff0001e3fc002f 0xabfffc00078ff000

def z1109 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xe7ff0001fffc002a 0x0b9ffc0007fff000

def z1110 : W := mkw 0xf722fa6400000000 0x03dc8be990000000 0xfffffffe0000001f 0xf3fffffff8000000

def z1111 : W := mkw 0x4121000041180000 0x0104840001046000 0xe6270000e39c0002 0x0b989c00038e7000

def z1112 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x1e3ffc7e13fcf9ff 0xfc78fff1f84ff3e7

def z1113 : W := mkw 0x2202fffe2087f9dd 0x1c880bfff8821fe7 0x0000fffe0003f9d0 0x540003fff8000fe7

def z1114 : W := mkw 0xddbd0000df380000 0x2376f400037ce000 0xfe3f0001ff9c0027 0xabf8fc0007fe7000

def z1115 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f607e13fce1ee 0x9818fd81f84ff387

def z1116 : W := mkw 0xffb6ff6caa82d420 0x13fedbfdb2aa0b50 0xffffffffff80e03f 0xfbfffffffffe0380

def z1117 : W := mkw 0xffb6ff6c00805000 0x13fedbfdb0020140 0xfffffffe0380e01f 0xfbfffffff80e0380

def z1118 : W := mkw 0xddf50001cf580000 0x2377d400073d6000 0xffe70001ff9c0027 0xabff9c0007fe7000

def z1119 : W := mkw 0xffb6ff6c20028420 0x13fedbfdb0800a10 0xfffffffe0003061f 0xf3fffffff8000c18

def z1120 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xffff0001fffc01ff 0xbffffc0007fff007

def z1121 : W := mkw 0xddfd0081df790110 0x2377f402077de404 0xffff8381ffff002f 0xebfffe0e07fffc00

def z1122 : W := mkw 0xd56d0001df780000 0x2355b400077de000 0xe63f0001fffc002e 0x8b98fc0007fff000

def z1123 : W := mkw 0xd5250000cb180000 0x23549400032c6000 0xe6270000e3fc002a 0x8b989c00038ff000

def z1124 : W := mkw 0x2adafdbf34e7fffb 0x04ab6bf6fcd39fff 0x19d8ffff1c63fffd 0xf46763fffc718fff

def z1125 : W := mkw 0x49b6076c00000000 0x1126d81db0000000 0x19ff9fff1c031e3d 0xf467fe7ffc700c78

def z1126 : W := mkw 0xd52d0000db380000 0x2354b400036ce000 0xfe3f0001fffc002f 0xabf8fc0007fff000

def z1127 : W := mkw 0x9e9b3d2e9fa85e63 0x067a6cf4ba7ea179 0x1e1f1c0e1f801e04 0x20787c70387e0078

def z1128 : W := mkw 0xddfd058bdf790b52 0x2377f4162f7de42d 0xffff8f81ffff1fef 0xeffffe3e07fffc7f

def z1129 : W := mkw 0x020b303611ac78c9 0x04082cc0d846b1e3 0x063f607e03fce1fa 0x9c18fd81f80ff387

def z1130 : W := mkw 0x08d9058b15690b52 0x002364162c55a42d 0x1fdf9f8f1fe31ffd 0xf47f7e7e3c7f8c7f

def z1131 : W := mkw 0xffb6f26400000000 0x03fedbc990000000 0xfffff3fe0000001f 0xf3ffffcff8000000

def z1132 : W := mkw 0xffb6ff6caa028420 0x13fedbfdb2a80a10 0xffffffffec03e63f 0xffffffffffb00f98

def z1133 : W := mkw 0x00490093717fa9dd 0x0c0124024dc5fea7 0x00000001e07fe1e0 0x0c0000000781ff87

def z1134 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe3ffc01ff83fe3f 0xeff8fff007fe0ff8

def z1135 : W := mkw 0xddfd0001df780000 0x2377f400077de000 0xfe3f0001fffc0026 0x2bf8fc0007fff000

def z1136 : W := mkw 0x220af83630a6fce9 0x04882be0d8c29bf3 0x1818fc7f1c63fffd 0xf46063f1fc718fff

def z1137 : W := mkw 0xb600f800aa82d420 0x02d803e002aa0b50 0xfe18fc0fff83fe3f 0xfff863f03ffe0ff8

def z1138 : W := mkw 0x00490093517d29dd 0x0c0124024d45f4a7 0x00000000007c01c0 0x000000000001f007

def z1139 : W := mkw 0x4161000141580000 0x0105840005056000 0xe7e70001e3fc002b 0x8b9f9c00078ff000

def z1140 : W := mkw 0x08d0058b04410b52 0x002340162c11042d 0x19c09f8f1c031ff5 0xf467027e3c700c7f

def z1141 : W := mkw 0x0009000011280000 0x000024000044a000 0xe63f0001f3fc002f 0x8b98fc0007cff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z7,z8,z5,z9,z6]),(0,[z10,z11,z2,z3,z7,z5,z6]),(0,[z12,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z13,z3,z7,z5,z6]),(0,[z1,z2,z14,z3,z7,z5,z6]),(0,[z1,z15,z2,z16,z3,z7,z5])],[(0,[z17,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z18]),(0,[z1,z19,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z21,z6]),(0,[z1,z2,z3,z7,z22,z20,z6]),(0,[z1,z2,z3,z23,z7,z5,z6])],[(0,[z24,z1,z2,z3,z7,z20,z6]),(0,[z25,z1,z2,z3,z7,z5,z6]),(0,[z26,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z16,z16,z3,z7,z5])],[(0,[z1,z2,z3,z7,z27,z5,z6]),(1,[z1,z2,z28,z7,z5,z6]),(1,[z1,z2,z3,z7,z29,z6]),(0,[z1,z2,z3,z7,z29,z5,z6]),(0,[z1,z2,z14,z3,z30,z7,z6]),(0,[z31,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z16,z33,z3,z7,z5]),(0,[z1,z2,z3,z34,z7,z5,z6])],[(0,[z1,z2,z35,z3,z7,z5,z6]),(0,[z1,z2,z3,z36,z7,z5,z6]),(0,[z1,z2,z3,z37,z7,z5,z6]),(0,[z31,z1,z2,z38,z3,z7,z5])],[(0,[z1,z2,z3,z39,z7,z40,z6]),(0,[z41,z1,z2,z3,z7,z5,z6]),(0,[z42,z1,z2,z3,z7,z40,z6]),(0,[z43,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z44]),(0,[z45,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z16,z3,z7,z5,z9]),(0,[z1,z2,z46,z3,z7,z5,z6]),(0,[z47,z1,z2,z3,z7,z5,z32]),(0,[z48,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z49,z7,z5,z6])],[(0,[z50,z1,z2,z3,z7,z5,z6])]],
   [[(0,[z51,z1,z2,z3,z7,z5,z6]),(1,[z1,z3,z7,z20,z40,z6]),(0,[z1,z2,z3,z7,z40,z52,z6]),(0,[z1,z2,z3,z7,z40,z6,z32]),(0,[z53,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z54,z3,z7,z5,z6])],[(0,[z55,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z56,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z40,z32]),(0,[z1,z2,z57,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z58]),(0,[z1,z2,z3,z7,z7,z5,z32])],[(0,[z1,z59,z2,z3,z7,z5,z6]),(0,[z60,z1,z2,z3,z7,z5,z6]),(0,[z61,z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z3,z62,z7,z5,z6]),(0,[z63,z1,z2,z3,z7,z5,z32]),(0,[z64,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z65,z6])],[(0,[z1,z2,z3,z66,z7,z5,z32]),(0,[z1,z2,z67,z3,z7,z5,z6]),(0,[z1,z68,z3,z69,z7,z5,z6]),(0,[z1,z2,z3,z7,z70,z5,z6]),(0,[z1,z2,z71,z3,z72,z5,z6])],[(0,[z1,z2,z3,z73,z7,z5,z6]),(0,[z74,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z75,z7,z5,z6]),(0,[z1,z2,z76,z3,z7,z5,z6])],[(0,[z1,z77,z3,z7,z5,z40,z6]),(0,[z61,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z39,z5,z6,z32]),(0,[z1,z2,z3,z78,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z70,z5]),(0,[z79,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z80,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z81,z6])],[(0,[z1,z2,z3,z82,z7,z5,z6]),(0,[z1,z2,z83,z3,z7,z5,z6]),(0,[z1,z2,z84,z3,z7,z5,z6]),(0,[z1,z85,z2,z3,z7,z5,z6]),(0,[z1,z2,z86,z3,z7,z5,z6])],[(0,[z1,z2,z87,z3,z7,z5,z6]),(0,[z1,z2,z88,z3,z7,z5,z6]),(1,[z1,z2,z89,z3,z7,z6]),(0,[z1,z2,z3,z7,z40,z90,z6]),(0,[z1,z2,z3,z7,z91,z5,z6]),(0,[z1,z2,z3,z72,z7,z5,z32]),(0,[z1,z92,z2,z3,z7,z5,z32])]],
   [[(0,[z93,z1,z2,z3,z7,z5,z6]),(0,[z94,z2,z95,z3,z7,z5,z6]),(1,[z1,z96,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z97]),(0,[z1,z2,z14,z16,z3,z7,z5]),(0,[z98,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z39,z7,z20,z6]),(0,[z42,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z69,z7,z5,z52,z6]),(0,[z99,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z100,z3,z7,z5,z6]),(0,[z101,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z102,z3,z7,z5,z6]),(0,[z1,z2,z71,z3,z7,z5,z103])],[(0,[z104,z1,z2,z3,z7,z5,z6]),(0,[z0,z1,z2,z16,z3,z5,z6])],[(1,[z1,z2,z3,z7,z105,z6]),(0,[z1,z2,z3,z7,z5,z6,z106]),(0,[z1,z2,z3,z7,z107,z5,z6]),(0,[z1,z2,z3,z108,z109,z7,z5])],[(0,[z1,z110,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z111,z5,z6]),(0,[z1,z2,z16,z3,z112,z7,z5]),(0,[z113,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z108,z7,z5,z6]),(0,[z1,z2,z114,z3,z7,z5,z6]),(0,[z1,z2,z38,z3,z7,z6,z115])],[(0,[z1,z2,z3,z7,z5,z6,z116]),(0,[z1,z2,z3,z117,z7,z5,z6]),(0,[z1,z118,z2,z3,z7,z119,z6]),(0,[z1,z2,z3,z7,z5,z120,z6]),(0,[z121,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z122,z5,z6]),(0,[z1,z2,z123,z3,z7,z5,z6]),(0,[z99,z1,z2,z124,z7,z5,z6])],[(0,[z55,z2,z3,z7,z4,z5,z6]),(0,[z1,z2,z3,z7,z125,z5,z6]),(0,[z126,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z20,z6,z127]),(0,[z1,z2,z128,z3,z7,z5,z6]),(0,[z1,z2,z129,z7,z5,z6,z127]),(1,[z1,z2,z3,z7,z5,z130])]],
   [[(0,[z1,z2,z3,z7,z4,z5,z6]),(0,[z1,z2,z131,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z40,z132,z6]),(0,[z1,z2,z3,z7,z20,z6,z133]),(1,[z1,z2,z3,z7,z5,z103])],[(1,[z1,z19,z68,z7,z5,z6]),(0,[z1,z2,z3,z7,z20,z40,z6]),(0,[z1,z2,z3,z7,z134,z5,z6])],[(0,[z135,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z136,z3,z7,z5,z6]),(0,[z137,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z76,z3,z5,z6,z138])],[(0,[z1,z2,z3,z7,z5,z6,z139])],[(0,[z1,z2,z3,z140,z7,z5,z6]),(0,[z1,z2,z141,z3,z7,z5,z6]),(0,[z1,z2,z142,z3,z7,z5,z6]),(0,[z143,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z144,z3,z7,z20,z6])],[(0,[z145,z1,z2,z3,z7,z5,z6]),(0,[z146,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z147,z6]),(0,[z99,z1,z2,z3,z7,z20,z6])],[(0,[z1,z2,z3,z7,z148,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z149]),(0,[z1,z2,z150,z3,z7,z5,z6]),(0,[z151,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z152]),(0,[z153,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z154,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z155,z6]),(0,[z156,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z112,z7,z5,z157]),(0,[z1,z2,z124,z7,z5,z6,z127]),(0,[z1,z2,z158,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z32,z159]),(0,[z1,z2,z16,z3,z160,z7,z5])]],
   [[(0,[z1,z161,z2,z3,z7,z5,z6]),(0,[z51,z1,z2,z3,z7,z40,z6]),(0,[z47,z1,z2,z3,z7,z5,z162]),(0,[z1,z2,z163,z3,z7,z5,z6]),(0,[z1,z164,z2,z3,z7,z5,z6])],[(0,[z24,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z40,z9,z6]),(0,[z1,z2,z3,z7,z165,z5,z6]),(0,[z1,z2,z3,z69,z7,z5,z6]),(0,[z1,z2,z166,z3,z7,z5,z6]),(0,[z1,z167,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z168,z7,z5,z32])],[(0,[z1,z2,z3,z169,z7,z5,z6]),(0,[z1,z2,z170,z3,z7,z5,z6]),(0,[z1,z2,z171,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z40,z6,z162]),(0,[z1,z2,z3,z124,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z6,z172]),(0,[z1,z2,z173,z3,z7,z5,z6])],[(0,[z174,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z5,z175,z6]),(0,[z1,z2,z3,z7,z5,z176,z6]),(0,[z126,z2,z3,z7,z8,z5,z6]),(0,[z177,z1,z2,z3,z7,z178,z6]),(0,[z1,z2,z16,z3,z7,z5,z127]),(0,[z1,z2,z179,z3,z7,z5,z32])],[(0,[z1,z2,z3,z180,z7,z5,z6]),(0,[z181,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z178,z6]),(0,[z1,z2,z3,z7,z20,z20,z6]),(0,[z1,z2,z3,z7,z5,z182,z6]),(0,[z183,z1,z2,z3,z7,z5,z6]),(0,[z184,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z185,z3,z7,z5,z6])],[(0,[z186,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z187,z3,z109,z5,z6]),(0,[z1,z2,z3,z188,z7,z5,z6]),(0,[z1,z2,z38,z16,z3,z7,z5])],[(0,[z1,z2,z3,z7,z5,z189,z6]),(0,[z42,z1,z2,z3,z190,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z191]),(0,[z1,z2,z3,z7,z20,z6,z138]),(0,[z1,z118,z2,z3,z7,z5,z132]),(0,[z192,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z193,z5,z32])]],
   [[(0,[z1,z2,z3,z194,z7,z5,z6]),(0,[z1,z195,z2,z3,z7,z5,z32])],[(0,[z1,z2,z16,z68,z3,z7,z5]),(0,[z1,z2,z3,z7,z5,z52,z32]),(0,[z196,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z16,z3,z7,z20,z5]),(0,[z1,z197,z2,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z5,z52]),(0,[z1,z198,z2,z3,z7,z5,z6])],[(0,[z199,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z200,z6]),(0,[z1,z2,z3,z7,z5,z6,z201]),(0,[z1,z2,z3,z7,z40,z40,z6]),(1,[z1,z2,z14,z7,z202,z6])],[(0,[z51,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z6,z203]),(0,[z1,z2,z114,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z204,z5,z6]),(0,[z1,z2,z3,z205,z7,z5,z6])],[(0,[z206,z1,z77,z3,z7,z5,z6]),(0,[z1,z2,z3,z207,z7,z5,z6]),(0,[z208,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z209,z7,z5,z6]),(0,[z51,z1,z2,z114,z3,z7,z6]),(0,[z1,z2,z3,z124,z7,z20,z6]),(1,[z1,z2,z3,z7,z5,z210])],[(0,[z1,z2,z3,z7,z211,z5,z6]),(1,[z55,z212,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z213,z6]),(0,[z1,z2,z214,z187,z7,z5,z6]),(1,[z1,z2,z187,z109,z5,z6]),(0,[z1,z2,z71,z76,z3,z7,z6]),(0,[z1,z2,z16,z215,z3,z7,z5])]],
   [[(0,[z1,z2,z3,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z4,z40,z6]),(0,[z1,z2,z3,z216,z7,z5,z6]),(0,[z42,z1,z2,z3,z7,z5,z6]),(0,[z1,z19,z2,z16,z3,z7,z5]),(0,[z10,z1,z2,z3,z112,z5,z6]),(0,[z217,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z163,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z193,z5,z115])],[(0,[z218,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z219,z3,z7,z5,z6]),(0,[z24,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z5,z220,z6]),(0,[z42,z1,z2,z3,z221,z5,z6]),(0,[z222,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z223,z5,z6])],[(0,[z1,z2,z3,z7,z8,z5,z32]),(1,[z1,z2,z3,z7,z178,z6]),(0,[z1,z2,z3,z7,z224,z5,z6]),(0,[z1,z2,z3,z225,z7,z5,z6])],[(0,[z1,z2,z3,z226,z7,z5,z6]),(0,[z1,z2,z227,z3,z7,z5,z6]),(0,[z1,z3,z7,z5,z132,z6,z162]),(0,[z1,z2,z16,z3,z7,z5,z138]),(0,[z1,z2,z228,z3,z7,z5,z6])],[(0,[z2,z3,z39,z7,z4,z5,z6]),(0,[z229,z42,z2,z3,z7,z5,z6]),(0,[z10,z230,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z231,z6]),(0,[z1,z2,z232,z3,z7,z5,z6]),(0,[z1,z233,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z234,z7,z5,z6])],[(0,[z42,z1,z118,z2,z3,z7,z5]),(0,[z1,z235,z2,z3,z7,z231,z6])],[(0,[z1,z2,z3,z7,z236,z5,z6]),(0,[z237,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z112,z7,z5,z32]),(0,[z1,z2,z3,z238,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z7,z5,z239,z6]),(0,[z1,z2,z16,z3,z69,z7,z5]),(1,[z1,z235,z3,z112,z5,z6]),(0,[z1,z2,z114,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z240,z6])],[(0,[z24,z61,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z241]),(0,[z1,z2,z3,z69,z7,z40,z6]),(0,[z1,z2,z3,z7,z40,z6,z138]),(0,[z1,z2,z3,z7,z20,z52,z6]),(0,[z1,z2,z3,z7,z20,z6,z32]),(0,[z1,z2,z3,z7,z5,z132,z32]),(0,[z1,z2,z3,z242,z7,z5,z6])],[(0,[z1,z212,z2,z3,z7,z5,z6]),(0,[z1,z243,z2,z3,z7,z5,z6]),(0,[z244,z1,z2,z3,z7,z5,z6]),(0,[z245,z1,z2,z3,z7,z5,z6]),(0,[z42,z1,z2,z3,z7,z5,z246]),(0,[z1,z118,z3,z7,z5,z6,z162]),(0,[z1,z2,z3,z7,z5,z247,z6]),(0,[z1,z2,z71,z3,z7,z5,z32])],[(0,[z248,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z249,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z250,z6]),(0,[z1,z2,z3,z7,z251,z5,z6]),(0,[z1,z2,z3,z7,z5,z252,z6]),(1,[z1,z2,z71,z76,z3,z6])],[(0,[z1,z2,z170,z3,z66,z7,z6]),(0,[z1,z2,z171,z3,z66,z7,z6]),(1,[z1,z2,z3,z253,z7,z5]),(0,[z1,z2,z3,z7,z4,z20,z6]),(0,[z229,z2,z3,z7,z5,z90,z6]),(0,[z1,z2,z3,z254,z7,z5,z6]),(1,[z1,z2,z3,z7,z213,z6]),(0,[z255,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z256,z3,z7,z5,z6])],[(0,[z257,z1,z2,z3,z7,z5,z6]),(0,[z258,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z259,z3,z7,z20,z6]),(0,[z1,z2,z260,z3,z7,z5,z6]),(0,[z261,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z262,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z263,z6]),(0,[z1,z2,z142,z3,z112,z7,z5]),(0,[z1,z2,z136,z3,z7,z20,z6])],[(0,[z1,z2,z264,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z265,z3,z7,z5,z6]),(0,[z1,z2,z3,z253,z66,z7,z5]),(0,[z1,z2,z3,z7,z5,z266,z6]),(0,[z42,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z20,z90,z6]),(0,[z10,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z5,z6,z267]),(0,[z1,z2,z268,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z269]),(0,[z1,z2,z16,z129,z3,z7,z5]),(0,[z1,z2,z3,z7,z270,z5,z6])],[(0,[z271,z1,z2,z3,z7,z5,z6]),(0,[z94,z1,z2,z66,z7,z5,z6]),(0,[z1,z2,z3,z7,z40,z272,z6]),(0,[z145,z1,z2,z3,z7,z20,z6]),(1,[z1,z2,z3,z7,z5,z32])],[(0,[z273,z1,z2,z3,z7,z5,z6]),(0,[z274,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z9,z32]),(0,[z177,z1,z19,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z5,z275])],[(0,[z1,z2,z276,z3,z7,z5,z6]),(0,[z1,z2,z3,z277,z7,z5,z6]),(0,[z1,z235,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z278,z5,z6]),(0,[z279,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z114,z14,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z280,z6]),(0,[z177,z1,z3,z69,z7,z5,z6]),(1,[z11,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z20,z5,z6]),(0,[z1,z2,z281,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z282,z5,z6]),(1,[z229,z2,z3,z7,z5,z90]),(0,[z1,z2,z3,z69,z7,z20,z6]),(0,[z10,z1,z2,z3,z7,z111,z6]),(0,[z1,z235,z2,z3,z70,z5,z6]),(0,[z1,z2,z16,z3,z7,z5,z32])],[(0,[z1,z2,z3,z7,z5,z6,z283]),(1,[z1,z2,z3,z7,z111,z6])],[(0,[z1,z2,z284,z3,z7,z5,z6]),(0,[z177,z1,z2,z3,z7,z105,z6]),(0,[z285,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z286,z7,z5,z6]),(0,[z1,z2,z287,z16,z3,z7,z5])]],
   [[(0,[z1,z2,z288,z3,z7,z5,z6]),(0,[z1,z2,z187,z68,z7,z5,z6]),(0,[z289,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z290,z7,z5,z6])],[(0,[z1,z2,z291,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z4,z5]),(0,[z1,z195,z3,z7,z5,z40,z6]),(0,[z1,z2,z3,z7,z20,z132,z6]),(0,[z1,z118,z2,z3,z7,z5,z6]),(0,[z1,z292,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z246]),(0,[z1,z2,z3,z7,z40,z6,z293]),(0,[z1,z2,z129,z3,z7,z5,z127]),(0,[z294,z1,z2,z3,z7,z5,z32])],[(0,[z174,z2,z3,z66,z7,z5,z6]),(0,[z1,z2,z38,z3,z7,z193,z5])],[(0,[z55,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z16,z3,z30,z7,z5]),(0,[z99,z1,z2,z16,z3,z7,z5])],[(0,[z1,z212,z2,z3,z7,z295,z6]),(0,[z1,z3,z7,z20,z5,z40,z6]),(0,[z296,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z297,z6]),(0,[z1,z2,z3,z124,z7,z5,z6])],[(0,[z1,z2,z298,z3,z7,z5,z6]),(0,[z230,z1,z2,z3,z7,z5,z6]),(0,[z47,z1,z2,z3,z7,z5,z132])],[(0,[z1,z2,z299,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z300,z5,z6]),(0,[z94,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z5,z6,z301]),(0,[z206,z1,z2,z3,z7,z5,z6]),(0,[z31,z1,z2,z3,z7,z5,z115]),(0,[z302,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z303,z3,z7,z5,z6]),(0,[z1,z2,z304,z3,z7,z5,z6])]],
   [[(0,[z1,z11,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z109,z7,z5,z305])],[(0,[z186,z55,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z306]),(0,[z1,z2,z3,z307,z7,z5,z6]),(0,[z1,z2,z3,z308,z7,z5,z6]),(0,[z1,z2,z3,z7,z20,z309,z6]),(0,[z1,z2,z3,z7,z5,z310,z6]),(0,[z1,z2,z214,z3,z7,z5,z6]),(0,[z1,z2,z3,z109,z7,z5,z6]),(0,[z1,z2,z14,z3,z7,z202,z6])],[(0,[z1,z212,z2,z3,z7,z40,z6]),(0,[z311,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z20,z9,z6]),(0,[z1,z2,z3,z7,z5,z6,z312]),(0,[z313,z1,z2,z3,z7,z5,z6])],[(0,[z1,z314,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z315,z7,z5,z6]),(0,[z1,z2,z316,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z20,z6,z162]),(0,[z1,z2,z14,z3,z7,z5,z32]),(0,[z1,z2,z3,z30,z7,z5,z32])],[(0,[z1,z2,z3,z7,z40,z6,z115])],[(0,[z206,z1,z212,z3,z7,z5,z6]),(0,[z317,z1,z2,z3,z7,z5,z6])],[(0,[z126,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z318,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z319,z6]),(0,[z1,z2,z3,z320,z7,z5,z6])],[(0,[z1,z2,z77,z3,z7,z5,z6]),(0,[z24,z2,z3,z39,z7,z5,z6]),(0,[z51,z1,z2,z71,z3,z7,z6]),(0,[z47,z1,z3,z7,z5,z132,z6]),(0,[z1,z2,z321,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z322]),(1,[z1,z2,z3,z168,z5,z32]),(0,[z1,z323,z2,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z324,z7,z5,z6])],[(0,[z325,z1,z2,z3,z7,z5,z6]),(0,[z51,z1,z2,z3,z7,z9,z6]),(0,[z229,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z40,z32]),(0,[z1,z2,z3,z7,z5,z326,z6]),(0,[z1,z2,z187,z3,z7,z5,z32])],[(0,[z1,z212,z2,z3,z7,z327,z6]),(0,[z206,z1,z195,z3,z7,z5,z6]),(0,[z1,z2,z114,z3,z30,z7,z6])],[(0,[z51,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z109,z7,z5,z52,z6]),(0,[z1,z2,z3,z7,z328,z5,z6]),(0,[z1,z2,z3,z329,z7,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z330,z7,z5,z6]),(1,[z24,z2,z3,z39,z5,z6]),(0,[z1,z2,z259,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z331,z32])],[(0,[z1,z2,z332,z3,z7,z5,z6]),(0,[z1,z2,z3,z333,z7,z5,z6]),(0,[z1,z2,z334,z3,z7,z5,z6]),(0,[z64,z1,z2,z16,z3,z7,z5]),(0,[z1,z335,z2,z3,z7,z5,z6])],[(1,[z1,z77,z3,z7,z40,z6]),(0,[z1,z212,z2,z3,z7,z20,z6]),(0,[z94,z1,z2,z95,z7,z5,z6]),(0,[z1,z2,z3,z336,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z337]),(0,[z1,z2,z3,z329,z72,z7,z5]),(0,[z1,z2,z3,z7,z5,z338,z6])],[(0,[z1,z2,z3,z339,z7,z5,z6]),(0,[z1,z2,z89,z3,z7,z4,z6]),(0,[z1,z2,z89,z3,z7,z5,z6]),(1,[z51,z2,z3,z7,z9,z6]),(0,[z1,z2,z3,z340,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z5,z162]),(0,[z1,z2,z341,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z342,z3,z7,z5,z6]),(0,[z1,z2,z3,z168,z7,z40,z6])],[(0,[z1,z2,z95,z3,z7,z5,z32]),(0,[z1,z118,z2,z3,z7,z40,z6]),(0,[z1,z343,z2,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z168,z7,z5])],[(0,[z1,z2,z3,z7,z5,z344,z6]),(1,[z1,z2,z3,z7,z5,z345]),(0,[z126,z1,z2,z3,z7,z20,z6]),(0,[z47,z1,z2,z3,z7,z297,z6]),(0,[z1,z2,z346,z3,z7,z5,z6])],[(0,[z325,z1,z2,z77,z3,z7,z5]),(0,[z1,z2,z16,z3,z66,z7,z5]),(0,[z1,z2,z3,z7,z5,z347,z6]),(0,[z1,z348,z2,z3,z7,z5,z6]),(0,[z1,z2,z349,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z350]),(0,[z351,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z352,z7,z5,z6]),(0,[z126,z1,z2,z114,z3,z7,z6]),(0,[z177,z1,z2,z68,z7,z5,z6]),(0,[z1,z2,z3,z7,z40,z202,z6])],[(0,[z353,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z354,z5,z6]),(0,[z355,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z356,z6]),(0,[z1,z2,z3,z7,z20,z357,z6]),(1,[z1,z2,z3,z7,z20,z32]),(0,[z1,z2,z3,z7,z20,z193,z6]),(0,[z1,z2,z3,z358,z7,z5,z6]),(0,[z1,z2,z114,z3,z7,z202,z6])],[(0,[z1,z359,z2,z3,z7,z5,z6]),(0,[z99,z42,z1,z2,z3,z7,z5]),(0,[z10,z1,z2,z3,z7,z5,z360]),(0,[z1,z2,z3,z7,z193,z40,z6]),(0,[z361,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z362,z5,z6]),(1,[z1,z2,z3,z7,z363,z6]),(0,[z1,z195,z2,z3,z7,z40,z6]),(0,[z206,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z114,z16,z3,z7,z5])]],
   [[(0,[z61,z1,z2,z3,z7,z5,z6]),(1,[z61,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z7,z5,z364,z6]),(0,[z1,z2,z3,z168,z5,z6,z32]),(0,[z184,z1,z2,z3,z7,z5,z32])],[(0,[z1,z2,z214,z3,z7,z40,z6]),(0,[z1,z2,z3,z109,z7,z40,z6]),(0,[z1,z2,z3,z365,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z130]),(0,[z1,z2,z38,z3,z7,z5,z32])],[(0,[z366,z1,z2,z3,z7,z5,z6]),(1,[z1,z367,z3,z7,z5,z6]),(0,[z1,z2,z3,z368,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z103]),(0,[z1,z2,z3,z7,z5,z32,z58]),(0,[z1,z2,z16,z3,z7,z193,z5]),(0,[z369,z1,z2,z3,z7,z5,z6])],[(0,[z370,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z371])],[(0,[z1,z2,z3,z372,z7,z5,z6]),(0,[z1,z2,z68,z3,z7,z5,z32]),(1,[z1,z2,z3,z7,z5,z157]),(0,[z1,z2,z3,z168,z7,z20,z6]),(0,[z296,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z129,z3,z7,z5,z32])],[(0,[z1,z118,z2,z3,z7,z20,z6]),(0,[z99,z1,z2,z3,z7,z5,z127]),(0,[z31,z1,z2,z3,z7,z5,z6])],[(0,[z186,z1,z77,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z373]),(0,[z1,z2,z3,z7,z5,z6,z374]),(0,[z1,z2,z3,z375,z7,z5,z6]),(0,[z1,z19,z2,z3,z7,z213,z6]),(0,[z1,z2,z3,z7,z5,z376,z6]),(0,[z1,z2,z3,z7,z377,z5,z6])],[(0,[z1,z2,z77,z3,z7,z40,z6]),(0,[z378,z1,z2,z3,z7,z5,z6]),(0,[z1,z118,z2,z3,z7,z379,z6]),(0,[z1,z380,z2,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z381,z3,z7,z5,z6]),(0,[z47,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z382]),(0,[z1,z2,z30,z7,z5,z202,z6]),(0,[z1,z2,z3,z383,z7,z5,z6])],[(0,[z1,z2,z3,z7,z8,z40,z6]),(0,[z229,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z214,z3,z5,z52,z6]),(0,[z1,z2,z3,z7,z5,z6,z127]),(0,[z0,z1,z2,z3,z168,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z133])],[(0,[z186,z2,z77,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z7,z5,z6]),(0,[z1,z19,z2,z3,z7,z5,z32]),(0,[z1,z195,z2,z3,z7,z20,z6]),(0,[z1,z2,z384,z3,z7,z40,z6]),(0,[z0,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z40,z6]),(0,[z206,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z385,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z386])],[(0,[z1,z2,z3,z7,z5,z387,z6]),(0,[z63,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z388,z7,z5,z6]),(0,[z1,z2,z3,z66,z7,z5,z6]),(0,[z1,z2,z3,z389,z7,z5,z6]),(0,[z177,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z214,z3,z7,z20,z6]),(0,[z1,z2,z3,z109,z7,z20,z6]),(0,[z1,z2,z76,z3,z72,z7,z6])],[(0,[z390,z1,z2,z3,z7,z5,z6]),(0,[z1,z235,z2,z3,z112,z5,z6]),(0,[z1,z2,z3,z112,z7,z40,z6]),(0,[z1,z2,z391,z3,z7,z5,z6]),(0,[z1,z2,z392,z3,z7,z5,z6])],[(0,[z212,z2,z77,z3,z7,z5,z6]),(0,[z1,z2,z3,z340,z7,z40,z6]),(0,[z1,z2,z393,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z119,z6])]],
   [[(0,[z394,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z395]),(0,[z51,z1,z2,z3,z7,z8,z6]),(0,[z1,z2,z396,z3,z7,z5,z6]),(0,[z1,z2,z3,z397,z7,z5,z6]),(1,[z230,z2,z3,z7,z5,z6])],[(0,[z1,z2,z398,z3,z7,z5,z6]),(0,[z1,z2,z399,z3,z7,z5,z6]),(0,[z400,z1,z2,z3,z7,z5,z6]),(0,[z1,z401,z2,z3,z7,z5,z6]),(0,[z1,z2,z402,z3,z7,z5,z6]),(0,[z403,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z404,z3,z7,z5,z6]),(0,[z1,z2,z405,z3,z7,z5,z6]),(0,[z1,z2,z3,z406,z7,z5,z6])],[(0,[z1,z2,z407,z3,z7,z5,z6]),(0,[z1,z2,z3,z408,z7,z5,z6]),(0,[z1,z2,z3,z7,z409,z40,z6]),(0,[z1,z2,z3,z410,z7,z5,z6]),(0,[z411,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z412,z3,z7,z5,z6])],[(0,[z1,z2,z77,z3,z7,z20,z6]),(0,[z1,z2,z367,z3,z7,z5,z6]),(0,[z1,z413,z2,z3,z7,z5,z6])],[(0,[z55,z212,z2,z3,z7,z5,z6]),(0,[z414,z1,z2,z3,z7,z5,z6]),(0,[z415,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z416,z6]),(0,[z1,z2,z14,z7,z5,z202,z6]),(0,[z417,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z418,z3,z7,z5,z6]),(0,[z196,z1,z2,z16,z3,z7,z5])],[(0,[z1,z419,z2,z3,z7,z5,z6]),(0,[z229,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z420,z7,z5,z6])],[(0,[z1,z2,z421,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z422]),(0,[z42,z1,z2,z3,z7,z5,z90]),(0,[z42,z1,z2,z129,z3,z7,z5]),(0,[z423,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z316,z3,z7,z5,z6])],[(0,[z424,z1,z2,z3,z7,z5,z6]),(0,[z10,z1,z2,z3,z7,z5,z116]),(0,[z10,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z3,z425,z7,z5,z6]),(0,[z0,z1,z2,z3,z7,z20,z6]),(0,[z426,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z427,z6])]],
   [[(0,[z61,z1,z2,z3,z7,z40,z6]),(0,[z24,z1,z2,z3,z39,z5,z6]),(0,[z42,z2,z3,z7,z5,z6,z246]),(0,[z1,z2,z3,z7,z5,z428,z6]),(0,[z1,z2,z3,z429,z7,z5,z6])],[(0,[z1,z2,z3,z430,z7,z5,z6]),(0,[z1,z2,z431,z3,z7,z5,z6]),(0,[z126,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z432,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z138])],[(0,[z1,z2,z3,z112,z7,z20,z6])],[(0,[z1,z2,z399,z77,z3,z7,z5]),(1,[z94,z2,z95,z7,z5,z6]),(0,[z433,z1,z2,z3,z7,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z39,z7,z5,z32]),(0,[z1,z2,z3,z434,z7,z5,z6]),(0,[z1,z2,z435,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z360,z6]),(0,[z370,z1,z2,z3,z7,z40,z6]),(0,[z1,z436,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z437,z6]),(0,[z1,z438,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z439,z5,z6]),(0,[z229,z47,z1,z2,z3,z7,z5]),(0,[z31,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z20,z6,z115]),(0,[z1,z2,z3,z7,z5,z202,z32])],[(1,[z1,z212,z3,z7,z40,z6]),(0,[z1,z235,z2,z3,z7,z5,z32]),(0,[z1,z2,z129,z3,z124,z7,z5]),(0,[z1,z2,z228,z16,z3,z7,z5])],[(0,[z440,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z72,z5,z6,z138]),(0,[z1,z2,z3,z7,z5,z441,z6])]],
   [[(0,[z186,z1,z2,z3,z7,z442,z6]),(0,[z443,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z28,z7,z5,z6]),(0,[z47,z1,z2,z3,z7,z40,z6]),(0,[z444,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z445,z3,z7,z5,z6])],[(0,[z446,z1,z2,z3,z7,z5,z6]),(0,[z1,z447,z2,z3,z7,z5,z6]),(0,[z51,z126,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z448,z7,z5,z6])],[(0,[z449,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z450,z6]),(0,[z61,z1,z2,z3,z7,z5,z152]),(0,[z1,z2,z3,z7,z5,z451,z6])],[(0,[z2,z3,z7,z5,z90,z6,z246]),(0,[z452,z1,z2,z3,z7,z5,z6]),(0,[z10,z1,z2,z3,z7,z20,z6]),(1,[z1,z195,z3,z7,z40,z6]),(0,[z453,z1,z2,z3,z7,z5,z6]),(0,[z1,z454,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z168,z7,z5,z6]),(0,[z1,z2,z33,z3,z7,z5,z6])],[(0,[z61,z1,z2,z3,z7,z20,z6]),(0,[z1,z455,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z456]),(1,[z1,z118,z3,z7,z5,z162]),(0,[z1,z2,z3,z7,z5,z457,z6]),(0,[z1,z2,z3,z7,z5,z458,z6]),(0,[z1,z2,z3,z7,z5,z32,z201]),(0,[z1,z459,z2,z3,z7,z5,z6])],[(0,[z1,z212,z2,z16,z3,z7,z5]),(0,[z174,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z66,z7,z40,z6]),(0,[z1,z2,z3,z460,z7,z5,z6]),(0,[z126,z1,z2,z71,z3,z7,z6]),(0,[z461,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z462,z3,z7,z5,z6]),(0,[z1,z2,z463,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z5,z132]),(0,[z1,z2,z3,z7,z464,z5,z6]),(0,[z1,z2,z179,z3,z7,z5,z6])],[(1,[z1,z2,z170,z3,z7,z6]),(0,[z1,z2,z465,z3,z7,z5,z6]),(0,[z466,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z391,z3,z7,z40,z6]),(0,[z467,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z7,z5]),(0,[z31,z1,z2,z3,z7,z193,z6])],[(0,[z468,z1,z2,z3,z7,z5,z6]),(0,[z126,z1,z2,z3,z7,z9,z6]),(0,[z1,z2,z469,z3,z7,z5,z6]),(0,[z470,z1,z2,z3,z7,z5,z6]),(0,[z99,z1,z2,z3,z7,z5,z32]),(0,[z424,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z193,z6,z115])]],
   [[(0,[z2,z77,z3,z7,z4,z5,z6]),(0,[z471,z1,z2,z3,z7,z5,z6])],[(0,[z126,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z72,z7,z40,z6]),(0,[z31,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z472,z6]),(0,[z1,z2,z16,z76,z3,z7,z5]),(0,[z1,z2,z16,z3,z7,z5,z115]),(0,[z1,z2,z3,z7,z193,z5,z6])],[(0,[z2,z95,z3,z66,z7,z5,z6]),(0,[z94,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z473,z7,z5,z6]),(0,[z51,z1,z2,z14,z3,z7,z6]),(0,[z1,z235,z3,z112,z7,z5,z6]),(0,[z1,z195,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z30,z7,z40,z6]),(0,[z1,z2,z3,z375,z7,z20,z6])],[(0,[z1,z2,z474,z3,z7,z5,z6]),(0,[z1,z2,z475,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z52,z6]),(0,[z1,z476,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z32]),(0,[z1,z2,z3,z7,z477,z5,z6])],[(0,[z55,z1,z77,z3,z7,z5,z6]),(0,[z478,z1,z2,z3,z7,z5,z6]),(0,[z479,z1,z2,z3,z7,z5,z6]),(0,[z480,z1,z2,z3,z7,z5,z6]),(0,[z47,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z481,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z275]),(0,[z1,z2,z3,z482,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z483]),(0,[z1,z2,z3,z484,z7,z5,z6]),(0,[z1,z2,z3,z7,z20,z202,z6]),(0,[z1,z2,z485,z3,z7,z5,z6])],[(0,[z186,z1,z212,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z442,z6]),(0,[z1,z2,z486,z3,z7,z5,z6]),(0,[z229,z99,z1,z2,z3,z7,z5])],[(1,[z1,z2,z399,z3,z7,z5]),(0,[z487,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z40,z6,z172]),(0,[z488,z1,z2,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z489,z7,z5,z6]),(0,[z1,z2,z187,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z490,z5,z6]),(0,[z491,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z66,z7,z20,z6]),(0,[z1,z19,z2,z3,z7,z363,z6])],[(1,[z218,z1,z2,z3,z7,z5]),(0,[z1,z2,z3,z7,z5,z90,z6]),(0,[z1,z2,z3,z492,z7,z5,z6]),(0,[z1,z2,z493,z3,z7,z5,z6]),(0,[z494,z1,z2,z3,z7,z5,z6])],[(0,[z495,z1,z2,z3,z7,z5,z6])],[(1,[z1,z2,z3,z496,z7,z6]),(0,[z1,z2,z3,z7,z8,z5,z6]),(1,[z126,z2,z3,z7,z8,z6]),(0,[z1,z118,z2,z16,z3,z7,z5]),(0,[z1,z2,z497,z3,z7,z5,z6])],[(0,[z1,z2,z3,z72,z7,z20,z6]),(1,[z1,z2,z3,z7,z297,z6]),(1,[z47,z1,z3,z7,z5,z132])],[(0,[z1,z2,z498,z3,z7,z5,z6]),(0,[z1,z2,z3,z499,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z5,z6]),(0,[z51,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z5,z500,z6]),(0,[z1,z2,z384,z3,z7,z5,z6]),(0,[z1,z501,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z30,z7,z20,z6]),(0,[z1,z2,z502,z3,z7,z5,z6]),(0,[z503,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z504,z6]),(0,[z1,z2,z505,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z506,z5,z6]),(0,[z24,z55,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z72,z7,z6,z138])]],
   [[(0,[z507,z1,z2,z3,z7,z5,z6]),(0,[z508,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z187,z3,z5,z52,z6])],[(0,[z186,z1,z2,z3,z7,z27,z6]),(0,[z1,z2,z509,z3,z7,z5,z6]),(0,[z1,z2,z3,z112,z7,z5,z6]),(0,[z1,z2,z3,z7,z70,z5,z32]),(0,[z1,z2,z114,z30,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z510,z6]),(0,[z1,z2,z3,z7,z511,z5,z6])],[(0,[z218,z1,z2,z3,z66,z7,z5]),(0,[z1,z512,z2,z3,z7,z5,z6]),(0,[z229,z1,z118,z2,z3,z7,z5]),(1,[z177,z1,z69,z7,z5,z6]),(0,[z206,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z20,z513,z6]),(0,[z1,z2,z16,z3,z124,z7,z5]),(0,[z514,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z76,z3,z7,z5,z32])],[(1,[z1,z2,z3,z7,z442,z6]),(0,[z515,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z132,z6]),(0,[z1,z2,z3,z7,z5,z516,z6]),(0,[z1,z2,z3,z7,z5,z81,z32])],[(0,[z1,z2,z517,z3,z7,z5,z6]),(0,[z1,z2,z3,z39,z7,z5,z345]),(0,[z1,z2,z187,z3,z7,z20,z6]),(0,[z1,z2,z3,z429,z7,z20,z6]),(0,[z1,z2,z214,z16,z3,z7,z5]),(1,[z1,z2,z3,z329,z7,z5])],[(0,[z518,z1,z2,z3,z7,z5,z6]),(0,[z174,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z519,z6]),(0,[z1,z2,z3,z520,z7,z5,z6]),(0,[z1,z19,z2,z68,z7,z5,z6]),(0,[z1,z2,z3,z7,z409,z5,z6]),(0,[z521,z1,z2,z3,z7,z5,z6])],[(0,[z229,z1,z2,z3,z7,z5,z246]),(0,[z1,z2,z522,z3,z7,z5,z6])],[(0,[z229,z1,z2,z3,z7,z5,z90]),(0,[z184,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z523,z6])]],
   [[(0,[z186,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z6,z524]),(0,[z1,z2,z38,z3,z7,z40,z6]),(0,[z1,z2,z215,z3,z7,z5,z6])],[(0,[z1,z2,z3,z525,z7,z5,z6]),(0,[z99,z1,z2,z3,z124,z7,z5]),(0,[z1,z2,z3,z7,z526,z5,z6])],[(0,[z1,z2,z77,z16,z3,z7,z5]),(0,[z527,z1,z2,z3,z7,z5,z6]),(0,[z528,z1,z2,z3,z7,z5,z6]),(0,[z10,z1,z2,z3,z7,z5,z6]),(0,[z10,z1,z2,z342,z7,z5,z6]),(1,[z1,z2,z3,z7,z5,z360]),(1,[z1,z2,z3,z7,z5,z305]),(0,[z1,z2,z114,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z529,z5,z6])],[(1,[z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z32,z246]),(0,[z1,z2,z68,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z530,z6]),(0,[z1,z2,z129,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z309,z6]),(0,[z531,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z532,z5,z6]),(0,[z121,z1,z2,z3,z7,z5,z32])],[(0,[z1,z2,z533,z3,z7,z5,z6]),(0,[z1,z2,z95,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z9,z6]),(0,[z1,z2,z3,z534,z7,z5,z6]),(0,[z1,z2,z3,z7,z535,z5,z6]),(1,[z1,z2,z3,z221,z5,z6]),(0,[z229,z1,z2,z16,z3,z7,z5]),(0,[z536,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z160,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z537,z6]),(0,[z1,z2,z3,z7,z190,z5,z6]),(0,[z1,z15,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z484,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z6,z162]),(0,[z1,z2,z3,z538,z7,z5,z6]),(0,[z31,z1,z2,z38,z3,z7,z6])],[(0,[z1,z2,z3,z7,z4,z5,z32]),(0,[z126,z1,z2,z3,z7,z8,z6]),(0,[z1,z2,z3,z7,z5,z539,z6]),(0,[z1,z2,z3,z7,z540,z5,z6]),(0,[z0,z1,z2,z16,z3,z7,z5]),(1,[z1,z2,z3,z7,z193,z115])],[(0,[z1,z2,z541,z3,z7,z5,z6]),(0,[z1,z2,z3,z542,z7,z5,z6])]],
   [[(0,[z1,z543,z2,z3,z7,z5,z6]),(0,[z51,z1,z96,z3,z7,z5,z6])],[(0,[z174,z1,z2,z3,z7,z20,z6]),(0,[z544,z1,z2,z3,z7,z5,z6]),(0,[z10,z1,z235,z3,z7,z5,z6])],[(0,[z1,z2,z545,z3,z7,z5,z6]),(0,[z1,z2,z3,z546,z7,z5,z6]),(0,[z1,z2,z16,z3,z72,z7,z5])],[(0,[z547,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z548,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z549,z5,z6]),(1,[z1,z2,z3,z7,z347,z6]),(0,[z184,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z550,z20,z6]),(0,[z1,z2,z3,z7,z5,z551,z6])],[(0,[z186,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z552,z6]),(0,[z1,z2,z3,z7,z5,z6,z345]),(0,[z51,z1,z2,z3,z72,z7,z6]),(0,[z1,z2,z3,z7,z20,z8,z6]),(0,[z177,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z187,z69,z7,z5,z6]),(0,[z1,z19,z68,z3,z7,z5,z6]),(0,[z1,z2,z38,z3,z7,z20,z6]),(0,[z1,z2,z214,z7,z5,z52,z6]),(0,[z553,z1,z2,z3,z7,z5,z6]),(0,[z294,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z554,z5,z6]),(0,[z1,z2,z3,z555,z7,z5,z6]),(0,[z1,z235,z2,z3,z7,z347,z6])],[(0,[z1,z2,z3,z7,z5,z556,z6]),(0,[z557,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z558,z7,z5,z6]),(0,[z10,z1,z3,z7,z70,z5,z6])],[(0,[z1,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z559,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z560,z5,z6]),(0,[z561,z1,z2,z3,z7,z5,z6]),(0,[z61,z1,z2,z3,z7,z5,z562]),(0,[z24,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z69,z7,z5,z32]),(0,[z1,z2,z68,z3,z7,z20,z6]),(0,[z1,z2,z129,z3,z7,z20,z6]),(0,[z1,z2,z563,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z7,z564,z5,z6]),(0,[z508,z1,z2,z3,z7,z40,z6])],[(0,[z1,z2,z16,z3,z7,z8,z5]),(0,[z1,z2,z565,z3,z7,z5,z6]),(0,[z361,z1,z2,z16,z3,z7,z5])],[(0,[z10,z1,z2,z3,z7,z539,z6]),(0,[z10,z1,z2,z16,z3,z7,z5])],[(0,[z61,z1,z2,z16,z3,z7,z5]),(1,[z1,z2,z3,z7,z539,z6])],[(0,[z1,z2,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z27,z6]),(0,[z55,z1,z212,z3,z7,z5,z6]),(0,[z1,z566,z2,z3,z7,z5,z6]),(0,[z1,z2,z71,z3,z7,z40,z6]),(1,[z1,z2,z114,z30,z7,z6]),(0,[z1,z2,z3,z72,z7,z5,z6]),(0,[z1,z92,z2,z3,z7,z5,z6])],[(0,[z567,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z171,z3,z7,z6]),(0,[z1,z2,z3,z30,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z327,z6]),(1,[z1,z2,z3,z7,z295,z6]),(0,[z1,z2,z3,z7,z5,z6,z159]),(0,[z1,z2,z3,z7,z5,z6,z157]),(0,[z568,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z431,z3,z39,z7,z5]),(0,[z1,z2,z3,z7,z40,z6,z246]),(0,[z10,z1,z2,z28,z7,z5,z6]),(0,[z1,z2,z3,z7,z569,z40,z6]),(0,[z1,z570,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z571,z6])]],
   [[(0,[z174,z94,z2,z3,z7,z5,z6]),(0,[z1,z96,z2,z3,z7,z5,z6]),(0,[z1,z2,z572,z3,z7,z5,z6]),(0,[z177,z1,z2,z3,z7,z20,z6]),(0,[z31,z1,z2,z16,z3,z7,z5])],[(0,[z24,z2,z77,z3,z7,z5,z6]),(0,[z1,z2,z3,z496,z7,z4,z6]),(0,[z1,z2,z3,z496,z7,z5,z6])],[(0,[z573,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z210,z6])],[(0,[z1,z2,z16,z95,z3,z7,z5]),(0,[z1,z2,z3,z7,z574,z5,z6]),(1,[z1,z2,z3,z7,z5,z116]),(1,[z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z3,z575,z7,z5,z6]),(0,[z47,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z187,z3,z7,z5,z6]),(0,[z1,z2,z576,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z577,z6]),(0,[z1,z578,z2,z3,z7,z5,z6]),(0,[z1,z2,z548,z16,z3,z7,z5])],[(0,[z579,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z379,z6])],[(0,[z1,z2,z3,z7,z5,z6,z580]),(0,[z1,z2,z3,z7,z5,z562,z6]),(0,[z1,z235,z2,z3,z7,z40,z6]),(0,[z1,z2,z581,z3,z7,z5,z6]),(0,[z582,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z583,z3,z7,z5,z6]),(0,[z42,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z584,z5,z6]),(0,[z1,z2,z3,z585,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z331,z6])],[(0,[z51,z1,z367,z3,z7,z5,z6]),(0,[z1,z2,z586,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z223,z5,z32])]],
   [[(0,[z126,z1,z2,z14,z3,z7,z6]),(0,[z1,z2,z71,z3,z7,z20,z6]),(0,[z47,z1,z2,z3,z7,z29,z6]),(0,[z1,z587,z2,z3,z7,z5,z6])],[(0,[z61,z2,z3,z7,z4,z5,z6]),(0,[z1,z2,z3,z221,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z588,z6]),(0,[z1,z2,z589,z3,z7,z5,z6])],[(0,[z1,z2,z71,z3,z7,z6,z138])],[(0,[z1,z2,z3,z590,z7,z5,z6]),(1,[z1,z2,z3,z7,z327,z6]),(0,[z1,z2,z95,z3,z7,z5,z6]),(0,[z591,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z592]),(0,[z1,z2,z593,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z32,z162]),(0,[z1,z2,z71,z3,z7,z377,z5]),(0,[z1,z2,z3,z7,z5,z594,z6])],[(0,[z1,z2,z3,z7,z5,z272,z6]),(0,[z1,z2,z3,z595,z7,z5,z6]),(0,[z596,z1,z2,z3,z7,z5,z6]),(0,[z597,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z598])],[(1,[z1,z2,z3,z7,z5,z152]),(0,[z1,z3,z112,z7,z70,z5,z6])],[(0,[z55,z1,z2,z3,z7,z40,z6]),(0,[z1,z19,z2,z69,z7,z5,z6]),(0,[z1,z2,z3,z599,z7,z5,z6]),(0,[z1,z2,z3,z7,z231,z5,z6]),(1,[z1,z2,z16,z3,z7,z40])],[(0,[z1,z2,z3,z253,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z600,z6]),(0,[z601,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z602,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z16,z3,z5,z6,z32])]],
   [[(0,[z1,z212,z2,z3,z7,z5,z32]),(0,[z177,z1,z2,z69,z7,z5,z6]),(0,[z1,z2,z603,z3,z7,z5,z6])],[(0,[z94,z1,z2,z3,z7,z40,z6]),(0,[z1,z235,z2,z3,z7,z20,z6]),(1,[z1,z2,z3,z7,z379,z6]),(0,[z1,z2,z3,z7,z5,z32,z382]),(0,[z1,z2,z16,z3,z7,z5,z65])],[(0,[z184,z1,z2,z3,z7,z5,z6]),(0,[z174,z1,z2,z66,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z604,z6]),(0,[z1,z2,z3,z605,z7,z5,z6]),(0,[z1,z2,z3,z7,z550,z5,z6]),(0,[z1,z2,z3,z7,z5,z32,z127]),(1,[z1,z2,z3,z7,z377,z5]),(0,[z606,z1,z2,z3,z7,z5,z6])],[(0,[z186,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z607,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z608,z5,z6]),(1,[z42,z2,z3,z7,z5,z246]),(0,[z1,z2,z3,z609,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z20,z6]),(0,[z610,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z187,z16,z3,z7,z5]),(0,[z1,z2,z611,z3,z7,z5,z6]),(0,[z1,z2,z38,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z612,z6]),(0,[z1,z2,z3,z7,z5,z6,z613]),(0,[z1,z2,z2,z3,z7,z40,z6]),(0,[z1,z2,z214,z3,z7,z5,z210]),(0,[z1,z2,z3,z7,z614,z5,z6])],[(0,[z615,z1,z2,z3,z7,z5,z6]),(0,[z1,z616,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z293]),(0,[z1,z2,z14,z3,z7,z40,z6])],[(0,[z1,z2,z68,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z5,z40]),(0,[z617,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z129,z3,z7,z5,z6]),(0,[z1,z436,z2,z16,z3,z7,z5])],[(0,[z618,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z619,z6]),(0,[z206,z1,z3,z7,z20,z5,z6]),(0,[z1,z2,z620,z3,z7,z5,z6])]],
   [[(0,[z621,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z622,z6]),(0,[z1,z2,z16,z3,z7,z5,z202]),(0,[z99,z1,z2,z129,z7,z5,z6])],[(0,[z623,z1,z2,z3,z7,z5,z6]),(0,[z1,z624,z2,z3,z7,z5,z6]),(0,[z279,z1,z2,z3,z7,z5,z32])],[(0,[z1,z2,z3,z625,z7,z5,z6]),(0,[z55,z1,z2,z3,z7,z20,z6]),(0,[z626,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z627,z7,z5,z6]),(0,[z1,z2,z3,z7,z20,z5,z32]),(0,[z1,z2,z3,z7,z5,z6,z628]),(0,[z1,z2,z3,z629,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z630,z6])],[(0,[z1,z2,z631,z3,z7,z5,z6]),(0,[z1,z2,z632,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z633,z6])],[(0,[z1,z2,z3,z7,z22,z5,z6]),(0,[z94,z1,z2,z3,z7,z20,z6]),(0,[z47,z42,z1,z2,z3,z7,z5]),(0,[z1,z19,z2,z3,z7,z5,z6]),(1,[z206,z1,z3,z7,z20,z6])],[(0,[z1,z2,z634,z3,z7,z5,z6]),(1,[z0,z1,z2,z16,z3,z5])],[(0,[z1,z2,z3,z7,z295,z5,z6]),(0,[z177,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z119,z5,z6]),(0,[z1,z118,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z635,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z115])]],
   [[(0,[z174,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z70,z40,z6]),(0,[z1,z2,z3,z636,z7,z5,z6]),(0,[z1,z2,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z357,z5,z6]),(0,[z1,z2,z3,z637,z7,z5,z6]),(0,[z1,z2,z603,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z638,z5,z6])],[(0,[z1,z2,z3,z7,z5,z639,z6]),(0,[z1,z2,z3,z7,z640,z5,z6]),(0,[z1,z2,z641,z3,z7,z5,z6]),(0,[z1,z2,z76,z3,z7,z40,z6]),(0,[z1,z2,z14,z3,z7,z20,z6]),(1,[z1,z2,z3,z108,z7,z5]),(0,[z1,z2,z642,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z643,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z644]),(0,[z1,z2,z3,z7,z5,z32,z138])],[(0,[z186,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z95,z3,z7,z40,z6]),(0,[z1,z2,z645,z3,z7,z5,z6]),(1,[z1,z2,z3,z39,z5,z32]),(0,[z26,z1,z2,z3,z7,z20,z6]),(0,[z1,z2,z646,z3,z7,z5,z6]),(0,[z1,z2,z3,z124,z7,z5,z32])],[(0,[z1,z647,z2,z3,z7,z5,z6]),(1,[z174,z2,z66,z7,z5,z6]),(0,[z648,z1,z2,z3,z7,z5,z6]),(0,[z47,z1,z118,z3,z7,z5,z6]),(0,[z1,z2,z187,z109,z7,z5,z6])],[(1,[z1,z2,z3,z190,z5,z6]),(0,[z1,z195,z2,z16,z3,z7,z5]),(0,[z206,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z72,z7,z5,z130])],[(0,[z1,z2,z649,z3,z7,z5,z6]),(1,[z1,z2,z3,z4,z5,z32]),(0,[z1,z2,z3,z7,z40,z6,z127]),(0,[z1,z2,z100,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z650,z5,z6]),(1,[z99,z1,z2,z124,z7,z5]),(0,[z651,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z652,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z105,z5,z6]),(0,[z1,z2,z3,z7,z653,z5,z6]),(1,[z1,z2,z214,z5,z52,z6]),(0,[z1,z2,z214,z3,z7,z5,z32]),(0,[z1,z2,z3,z109,z7,z5,z32]),(0,[z1,z2,z71,z3,z7,z5,z6]),(0,[z480,z1,z2,z3,z7,z5,z32])]],
   [[(0,[z1,z2,z3,z7,z5,z654,z6]),(0,[z1,z2,z214,z3,z7,z5,z275])],[(0,[z1,z2,z3,z655,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z656,z6]),(0,[z657,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z658,z7,z5,z6]),(0,[z1,z2,z659,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z660,z6]),(0,[z126,z1,z2,z3,z72,z7,z6]),(0,[z229,z1,z2,z129,z3,z7,z5]),(0,[z1,z661,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z569,z5,z6]),(0,[z1,z2,z71,z76,z3,z5,z6])],[(1,[z1,z2,z431,z3,z7,z5]),(0,[z1,z2,z16,z3,z234,z7,z5])],[(0,[z1,z2,z3,z7,z70,z20,z6]),(0,[z1,z2,z3,z7,z5,z662,z6]),(0,[z1,z2,z3,z663,z7,z5,z6]),(0,[z1,z2,z3,z320,z7,z5,z32])],[(0,[z1,z2,z77,z3,z7,z5,z32]),(0,[z1,z2,z3,z39,z7,z5,z6]),(0,[z1,z2,z16,z3,z39,z7,z5]),(0,[z1,z2,z3,z7,z5,z90,z32]),(0,[z1,z2,z76,z3,z7,z20,z6]),(0,[z1,z664,z2,z3,z7,z5,z6])],[(1,[z1,z2,z342,z7,z5,z6])],[(1,[z186,z77,z3,z7,z5,z6]),(0,[z174,z1,z2,z95,z7,z5,z6]),(0,[z229,z1,z2,z3,z7,z5,z32]),(0,[z665,z1,z2,z3,z7,z5,z6]),(0,[z177,z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z666,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z202,z6]),(0,[z1,z2,z3,z7,z5,z667,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z32]),(0,[z1,z2,z3,z7,z20,z6,z246]),(0,[z1,z2,z3,z7,z5,z668,z6]),(0,[z1,z235,z2,z3,z7,z5,z6])],[(0,[z1,z212,z3,z7,z5,z40,z6]),(0,[z669,z1,z2,z3,z7,z5,z6]),(0,[z670,z1,z2,z3,z7,z5,z6]),(0,[z671,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z672,z5,z6]),(1,[z1,z2,z142,z3,z7,z5]),(0,[z1,z2,z16,z3,z109,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z32]),(0,[z1,z673,z2,z3,z7,z5,z6])],[(0,[z674,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z675,z7,z5,z6]),(0,[z1,z2,z676,z3,z7,z5,z6]),(0,[z677,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z678,z6])],[(1,[z10,z1,z3,z70,z5,z6]),(0,[z151,z1,z2,z3,z7,z40,z6]),(0,[z679,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z680,z5,z6]),(0,[z1,z2,z681,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z32,z32]),(0,[z1,z2,z287,z3,z7,z5,z6]),(0,[z1,z682,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z683,z5,z6]),(0,[z1,z19,z2,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z40,z428,z6]),(0,[z1,z2,z3,z7,z5,z684,z6]),(0,[z685,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z72,z6,z138])],[(0,[z1,z2,z3,z7,z5,z6,z686]),(0,[z24,z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z687,z3,z7,z5,z6]),(0,[z1,z2,z68,z7,z5,z52,z6]),(0,[z1,z2,z166,z3,z7,z40,z6])],[(0,[z1,z2,z3,z688,z7,z5,z6]),(0,[z1,z689,z2,z3,z7,z5,z6]),(0,[z1,z2,z214,z3,z109,z5,z6]),(0,[z1,z2,z71,z16,z3,z7,z5])]],
   [[(0,[z1,z2,z144,z3,z7,z5,z6]),(1,[z1,z2,z16,z3,z5,z32])],[(0,[z55,z1,z2,z3,z7,z5,z6]),(0,[z1,z118,z2,z3,z7,z5,z162]),(0,[z99,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z690,z3,z7,z5,z6]),(0,[z1,z2,z349,z3,z7,z5,z32]),(1,[z31,z1,z2,z38,z3,z7])],[(0,[z691,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z5,z562]),(0,[z1,z692,z2,z3,z7,z5,z6]),(0,[z1,z2,z693,z3,z7,z5,z6])],[(0,[z694,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z695,z5,z6]),(0,[z1,z2,z3,z7,z363,z5,z6]),(0,[z1,z2,z620,z3,z7,z20,z6]),(0,[z1,z2,z3,z696,z7,z5,z6])],[(1,[z325,z1,z2,z3,z7,z5]),(0,[z94,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z5,z246]),(1,[z1,z2,z16,z3,z7,z20]),(0,[z1,z2,z3,z7,z5,z513,z6]),(0,[z1,z2,z3,z7,z5,z6,z305])],[(0,[z697,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z698,z7,z5,z6]),(0,[z0,z1,z2,z3,z39,z5,z6]),(0,[z51,z2,z3,z7,z5,z9,z6]),(0,[z1,z2,z3,z7,z5,z6,z6]),(0,[z1,z2,z16,z3,z7,z5,z90]),(0,[z1,z2,z141,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z699,z5,z6]),(0,[z1,z2,z3,z7,z5,z700,z6]),(0,[z1,z2,z3,z7,z5,z32,z115]),(0,[z701,z1,z2,z3,z7,z5,z6])],[(0,[z61,z1,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z702,z7,z5,z6]),(1,[z1,z2,z129,z7,z5,z127]),(1,[z1,z2,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z703,z5,z6])],[(0,[z1,z704,z2,z3,z7,z5,z6]),(0,[z1,z2,z705,z3,z7,z5,z6]),(0,[z706,z1,z2,z3,z7,z5,z6]),(0,[z10,z1,z2,z3,z70,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z16,z3,z7,z442]),(0,[z245,z1,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z707,z6]),(0,[z1,z2,z3,z708,z7,z5]),(0,[z1,z2,z16,z3,z20,z32]),(0,[z1,z92,z3,z7,z5,z201])],[(0,[z1,z2,z3,z7,z709,z6])],[(0,[z1,z710,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z20,z562]),(0,[z1,z711,z3,z7,z5,z6])],[(0,[z121,z2,z3,z7,z5,z246]),(0,[z1,z2,z3,z7,z111,z32]),(0,[z1,z2,z179,z7,z5,z382]),(0,[z1,z2,z16,z712,z3,z5])],[(0,[z1,z2,z713,z3,z7,z6]),(0,[z0,z1,z2,z431,z3,z5]),(0,[z1,z2,z3,z7,z5,z714]),(0,[z206,z1,z3,z7,z20,z6]),(0,[z1,z2,z179,z7,z5,z127])],[(0,[z1,z2,z3,z7,z715,z6]),(1,[z2,z3,z716,z5,z6]),(0,[z1,z2,z717,z7,z5,z6]),(0,[z42,z2,z3,z7,z5,z718]),(0,[z1,z2,z3,z7,z719,z6]),(0,[z1,z2,z16,z3,z490,z5]),(0,[z0,z1,z2,z16,z3,z5])],[(0,[z1,z2,z129,z7,z20,z127])],[(0,[z1,z2,z171,z3,z253,z7]),(0,[z1,z720,z3,z7,z5,z6]),(0,[z1,z2,z3,z538,z5,z32]),(0,[z1,z721,z3,z7,z5,z6]),(0,[z1,z2,z712,z3,z5,z32]),(0,[z1,z2,z16,z3,z7,z722])]],
   [[(0,[z212,z77,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z723,z6]),(0,[z1,z2,z170,z3,z7,z32]),(0,[z42,z2,z3,z188,z7,z5])],[(0,[z1,z724,z3,z7,z5,z6]),(0,[z61,z2,z89,z3,z4,z6]),(0,[z1,z2,z3,z7,z725,z6]),(0,[z1,z3,z7,z148,z40,z6]),(1,[z1,z3,z7,z5,z726]),(0,[z1,z3,z7,z5,z727,z32]),(0,[z2,z3,z7,z5,z728,z32]),(0,[z1,z2,z228,z3,z7,z65]),(0,[z1,z2,z38,z729,z3,z7])],[(0,[z1,z730,z3,z7,z5,z6]),(0,[z2,z3,z716,z4,z5,z6]),(0,[z1,z2,z3,z7,z731,z6]),(0,[z1,z2,z16,z3,z7,z119]),(0,[z1,z2,z3,z7,z732,z32])],[(0,[z1,z2,z3,z7,z5,z733]),(0,[z174,z2,z66,z7,z5,z6]),(0,[z1,z2,z28,z7,z20,z6]),(0,[z1,z2,z3,z734,z7,z6])],[(0,[z1,z2,z3,z7,z5,z735]),(0,[z2,z3,z39,z716,z5,z6]),(0,[z1,z96,z3,z7,z40,z6]),(0,[z151,z2,z3,z7,z9,z6]),(0,[z736,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z484,z6,z138])],[(0,[z2,z3,z7,z5,z90,z718]),(0,[z177,z1,z69,z7,z178,z6]),(0,[z1,z2,z3,z429,z513,z6]),(0,[z99,z1,z2,z124,z7,z5]),(0,[z1,z2,z712,z3,z7,z5])],[(0,[z1,z2,z3,z7,z5,z737])],[(0,[z1,z2,z738,z3,z7,z5]),(0,[z1,z2,z3,z7,z5,z739]),(0,[z1,z2,z740,z3,z5,z6]),(0,[z1,z2,z3,z741,z40,z6]),(0,[z742,z2,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z430,z5,z32]),(0,[z1,z3,z7,z20,z743,z6]),(0,[z1,z3,z7,z5,z726,z6]),(0,[z1,z2,z744,z7,z5,z6]),(0,[z1,z2,z16,z3,z205,z5])],[(0,[z1,z616,z3,z7,z40,z6]),(0,[z64,z2,z3,z7,z5,z90])],[(0,[z1,z3,z7,z40,z441,z6]),(0,[z1,z413,z3,z7,z20,z6]),(0,[z1,z2,z187,z109,z5,z305]),(0,[z480,z1,z3,z7,z5,z331])],[(0,[z55,z212,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z745,z6]),(0,[z1,z2,z3,z746,z5,z6]),(0,[z1,z2,z3,z7,z5,z747]),(0,[z1,z2,z3,z7,z40,z130]),(0,[z1,z2,z187,z109,z5,z6]),(0,[z99,z1,z2,z744,z7,z5])],[(0,[z1,z2,z3,z7,z748,z6]),(0,[z94,z2,z16,z95,z7,z5]),(0,[z1,z2,z3,z496,z4,z32]),(0,[z1,z2,z3,z7,z40,z103]),(0,[z1,z2,z3,z749,z5,z6])],[(0,[z1,z2,z3,z750,z7,z5]),(0,[z24,z2,z3,z39,z40,z6]),(0,[z1,z2,z3,z7,z5,z751]),(0,[z1,z2,z114,z16,z30,z7]),(0,[z1,z2,z3,z752,z7,z5]),(0,[z1,z2,z3,z7,z753,z6])],[(0,[z186,z77,z3,z7,z5,z6]),(0,[z754,z1,z3,z7,z5,z6]),(0,[z1,z2,z3,z755,z7,z5]),(0,[z126,z2,z3,z7,z8,z32]),(0,[z1,z2,z3,z190,z5,z246])],[(0,[z1,z314,z3,z7,z40,z6]),(0,[z1,z2,z756,z3,z7,z6]),(0,[z1,z2,z3,z190,z5,z90]),(0,[z1,z3,z7,z40,z457,z6]),(0,[z1,z3,z7,z40,z458,z6]),(0,[z1,z2,z3,z7,z297,z32]),(0,[z1,z2,z3,z757,z5,z6])]],
   [[(0,[z1,z96,z3,z7,z20,z6]),(0,[z1,z758,z69,z7,z5,z6]),(0,[z1,z2,z3,z7,z231,z6]),(0,[z1,z2,z142,z3,z7,z5])],[(0,[z424,z2,z33,z3,z7,z5]),(0,[z1,z2,z729,z3,z7,z115])],[(0,[z1,z2,z759,z3,z7,z6]),(0,[z1,z543,z3,z7,z40,z6]),(0,[z10,z1,z342,z70,z5,z6]),(0,[z1,z2,z3,z7,z223,z58])],[(0,[z1,z2,z760,z3,z7,z6]),(0,[z2,z3,z4,z5,z81,z32]),(0,[z1,z2,z3,z761,z7,z6])],[(0,[z51,z2,z3,z7,z9,z32]),(0,[z177,z1,z69,z7,z5,z32]),(0,[z47,z1,z3,z7,z29,z132]),(0,[z1,z2,z30,z7,z762,z6]),(0,[z1,z2,z3,z72,z6,z138])],[(0,[z1,z2,z3,z7,z442,z32]),(0,[z1,z2,z3,z7,z763,z6]),(0,[z1,z2,z764,z3,z5,z6]),(0,[z1,z2,z3,z484,z6,z293]),(0,[z1,z2,z3,z7,z5,z726])],[(0,[z765,z2,z3,z7,z5,z6]),(0,[z1,z2,z485,z3,z5,z32]),(0,[z1,z2,z3,z34,z5,z32])],[(0,[z1,z2,z3,z169,z5,z32]),(0,[z1,z2,z3,z7,z766,z6]),(0,[z1,z2,z3,z7,z20,z130]),(0,[z1,z2,z71,z76,z3,z6])]],
   [[(0,[z1,z3,z767,z70,z5,z6]),(0,[z1,z2,z3,z7,z20,z103])],[(0,[z1,z2,z3,z768,z7,z5]),(0,[z1,z2,z3,z7,z5,z562]),(0,[z24,z2,z3,z39,z20,z6]),(0,[z126,z2,z16,z3,z7,z8]),(0,[z769,z1,z2,z3,z7,z5]),(0,[z1,z3,z7,z5,z770,z6]),(0,[z1,z771,z3,z7,z5,z32])],[(0,[z772,z1,z2,z3,z7,z5]),(0,[z1,z419,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z773,z6])],[(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z2,z3,z7,z775,z6]),(0,[z1,z2,z407,z5,z52,z6]),(0,[z1,z2,z3,z7,z776,z6]),(0,[z1,z2,z3,z7,z777,z6]),(0,[z1,z2,z71,z3,z734,z6])],[(0,[z1,z235,z3,z112,z347,z6])],[(0,[z1,z2,z16,z3,z7,z5]),(0,[z174,z2,z170,z66,z7,z6]),(0,[z61,z2,z3,z4,z5,z32]),(0,[z1,z2,z3,z7,z5,z778]),(0,[z1,z2,z187,z16,z109,z5])],[(0,[z186,z77,z16,z3,z7,z5]),(0,[z55,z212,z3,z7,z295,z6]),(0,[z1,z2,z779,z7,z5,z6]),(0,[z1,z2,z3,z780,z7,z5]),(0,[z1,z2,z3,z7,z5,z781])],[(0,[z1,z2,z782,z3,z7,z5]),(0,[z11,z2,z3,z7,z5,z360]),(0,[z31,z1,z2,z349,z3,z7])]],
   [[(0,[z325,z1,z77,z3,z7,z40]),(0,[z1,z2,z89,z16,z3,z7]),(0,[z606,z2,z3,z39,z5,z6]),(0,[z1,z2,z3,z7,z783,z6])],[(0,[z229,z2,z3,z7,z5,z90]),(0,[z1,z118,z288,z3,z7,z5]),(0,[z47,z1,z2,z3,z190,z5]),(0,[z1,z2,z3,z784,z5,z6]),(0,[z1,z2,z3,z7,z785,z6]),(0,[z1,z2,z3,z7,z111,z360]),(0,[z1,z2,z3,z7,z786,z32])],[(0,[z1,z2,z787,z3,z7,z5]),(0,[z174,z2,z788,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z718]),(0,[z1,z2,z3,z7,z5,z789]),(0,[z1,z2,z3,z7,z790,z6]),(0,[z1,z2,z3,z7,z29,z6]),(0,[z1,z2,z3,z7,z40,z210]),(0,[z1,z2,z3,z7,z791,z5])],[(0,[z55,z212,z3,z7,z40,z6]),(0,[z1,z265,z3,z7,z40,z6]),(0,[z1,z2,z3,z792,z7,z6]),(0,[z1,z2,z3,z7,z5,z793]),(0,[z1,z2,z3,z7,z794,z6]),(0,[z1,z2,z3,z7,z40,z795]),(0,[z1,z232,z3,z7,z20,z6]),(0,[z279,z1,z2,z320,z7,z5]),(0,[z1,z2,z3,z7,z796,z6])],[(0,[z1,z2,z3,z749,z40,z6])],[(0,[z1,z2,z797,z7,z5,z6]),(0,[z1,z2,z3,z7,z347,z32]),(0,[z1,z2,z16,z3,z270,z5])],[(0,[z1,z276,z3,z7,z40,z6]),(0,[z1,z2,z3,z798,z7,z5]),(0,[z1,z2,z799,z3,z7,z32])],[(0,[z10,z1,z28,z70,z5,z6]),(0,[z1,z2,z3,z7,z5,z800]),(0,[z1,z3,z7,z20,z40,z6])]],
   [[(0,[z1,z801,z3,z7,z5,z6])],[(0,[z77,z3,z7,z569,z40,z6]),(0,[z1,z2,z3,z7,z5,z802]),(0,[z1,z2,z3,z7,z803,z6]),(0,[z206,z1,z16,z3,z7,z20]),(0,[z47,z1,z3,z7,z5,z726])],[(0,[z1,z284,z3,z7,z40,z6]),(0,[z1,z566,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z804,z6]),(0,[z1,z805,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z806,z6]),(0,[z1,z2,z729,z3,z7,z193])],[(0,[z1,z2,z3,z7,z807,z5]),(0,[z55,z212,z3,z7,z327,z6]),(0,[z1,z2,z3,z253,z7,z40]),(0,[z1,z2,z3,z7,z808,z6]),(0,[z1,z288,z3,z7,z40,z6]),(0,[z1,z2,z214,z757,z5,z6]),(0,[z1,z2,z3,z809,z5,z6])],[(0,[z1,z2,z3,z810,z5,z6]),(0,[z811,z2,z3,z7,z5,z6]),(0,[z1,z235,z3,z112,z40,z6]),(0,[z1,z2,z214,z16,z5,z52]),(0,[z64,z2,z548,z3,z7,z5])],[(0,[z2,z801,z3,z7,z5,z6]),(0,[z1,z2,z764,z3,z40,z6])],[(0,[z1,z2,z3,z7,z27,z32]),(0,[z812,z1,z2,z3,z7,z5]),(0,[z1,z2,z89,z3,z7,z6]),(0,[z1,z2,z3,z7,z5,z813]),(0,[z1,z2,z16,z3,z7,z347]),(0,[z1,z2,z3,z7,z20,z210])],[(0,[z1,z96,z3,z7,z5,z6]),(0,[z1,z2,z814,z3,z7,z5]),(0,[z55,z212,z3,z7,z20,z6]),(0,[z1,z2,z171,z3,z7,z32]),(0,[z51,z2,z646,z3,z7,z6]),(0,[z815,z2,z3,z7,z40,z6]),(0,[z1,z2,z676,z3,z5,z32]),(0,[z1,z2,z3,z72,z130,z138])]],
   [[(0,[z1,z2,z3,z7,z816,z6]),(0,[z1,z2,z109,z757,z5,z6]),(0,[z817,z2,z3,z7,z5,z32])],[],[(0,[z1,z2,z3,z7,z818,z6]),(0,[z1,z2,z3,z7,z819,z6]),(0,[z1,z2,z3,z7,z820,z6]),(0,[z1,z447,z3,z7,z40,z6]),(0,[z99,z1,z2,z3,z190,z5]),(0,[z1,z2,z3,z7,z105,z6]),(0,[z1,z2,z3,z72,z32,z138])],[(0,[z1,z2,z3,z7,z821,z6])],[(0,[z1,z2,z3,z499,z5,z32]),(0,[z1,z118,z3,z7,z119,z162])],[(0,[z1,z2,z3,z822,z7,z6]),(0,[z1,z2,z16,z342,z7,z5]),(0,[z1,z2,z3,z7,z40,z32]),(0,[z1,z92,z3,z7,z40,z32])],[(0,[z1,z2,z3,z823,z5,z6]),(0,[z1,z2,z3,z7,z824,z6]),(0,[z1,z2,z3,z7,z5,z825]),(0,[z1,z2,z3,z7,z826,z6]),(0,[z1,z2,z3,z7,z827,z6]),(0,[z1,z2,z3,z7,z40,z275]),(0,[z1,z828,z3,z7,z5,z6]),(1,[z1,z2,z3,z734,z6])],[(0,[z1,z2,z829,z7,z5,z6]),(0,[z830,z2,z3,z7,z5,z6]),(0,[z1,z92,z3,z7,z5,z162]),(0,[z1,z2,z3,z464,z5,z32]),(0,[z1,z2,z3,z7,z831,z32])]],
   [[(0,[z1,z2,z3,z7,z832,z6]),(0,[z24,z2,z3,z39,z5,z6]),(0,[z11,z2,z3,z7,z40,z6]),(0,[z11,z2,z3,z7,z5,z116]),(0,[z1,z235,z3,z112,z20,z6])],[(0,[z1,z833,z2,z3,z7,z5]),(0,[z229,z2,z3,z7,z40,z90])],[(0,[z186,z399,z77,z3,z7,z5]),(0,[z1,z834,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z111,z116]),(0,[z47,z1,z3,z7,z5,z331])],[(0,[z1,z212,z3,z7,z40,z32]),(0,[z2,z3,z39,z4,z5,z32])],[(0,[z1,z2,z3,z7,z5,z835]),(0,[z1,z2,z89,z3,z4,z32]),(0,[z1,z2,z3,z7,z836,z6])],[(0,[z1,z2,z3,z7,z5,z837]),(0,[z1,z2,z3,z7,z5,z838]),(0,[z51,z367,z3,z7,z9,z6]),(0,[z51,z2,z16,z3,z7,z9]),(0,[z192,z1,z3,z7,z20,z6])],[(0,[z1,z2,z839,z7,z5,z6]),(0,[z1,z2,z3,z7,z840,z6]),(0,[z1,z2,z3,z7,z5,z345]),(0,[z1,z118,z2,z3,z190,z5]),(0,[z1,z303,z3,z7,z20,z6])],[(0,[z801,z77,z3,z7,z5,z6])]],
   [[(0,[z55,z2,z3,z4,z5,z32]),(0,[z94,z2,z95,z7,z20,z6]),(0,[z1,z401,z3,z7,z40,z6]),(0,[z1,z2,z129,z226,z7,z5]),(0,[z1,z2,z16,z3,z7,z213]),(0,[z1,z195,z3,z7,z40,z32])],[(0,[z1,z2,z3,z7,z5,z841]),(0,[z1,z2,z3,z7,z842,z5]),(0,[z1,z2,z3,z7,z20,z32])],[(0,[z1,z96,z3,z7,z295,z6]),(0,[z1,z2,z3,z7,z5,z843]),(0,[z1,z2,z3,z7,z844,z5]),(0,[z1,z341,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z20,z275]),(0,[z845,z1,z2,z3,z7,z5])],[(0,[z1,z2,z3,z7,z5,z846]),(0,[z1,z2,z399,z3,z7,z40]),(0,[z1,z2,z3,z7,z847,z6]),(0,[z1,z2,z3,z7,z848,z6]),(0,[z1,z2,z3,z7,z849,z6]),(0,[z1,z2,z3,z7,z363,z6])],[(0,[z1,z2,z16,z3,z7,z178]),(0,[z11,z2,z3,z7,z20,z6]),(0,[z1,z2,z3,z368,z5,z32])],[(0,[z1,z77,z16,z3,z7,z40]),(0,[z1,z2,z3,z7,z850,z6]),(0,[z229,z2,z3,z7,z20,z90]),(0,[z1,z19,z16,z68,z7,z5]),(0,[z1,z2,z3,z7,z851,z6]),(0,[z1,z2,z3,z7,z5,z852])],[(0,[z1,z2,z853,z3,z7,z6]),(0,[z1,z2,z3,z7,z854,z6]),(0,[z1,z855,z3,z7,z5,z6]),(0,[z177,z1,z758,z7,z5,z6]),(0,[z1,z2,z3,z7,z856,z6]),(0,[z1,z118,z3,z7,z5,z726]),(0,[z1,z2,z3,z7,z857,z6]),(0,[z1,z2,z858,z3,z7,z5])],[(0,[z1,z2,z859,z3,z7,z5]),(0,[z1,z2,z3,z860,z7,z6]),(0,[z1,z2,z3,z7,z5,z861]),(0,[z1,z2,z3,z7,z5,z862]),(0,[z1,z3,z112,z767,z5,z6]),(0,[z863,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z864,z6])]],
   [[(0,[z1,z2,z3,z7,z865,z6]),(0,[z1,z2,z16,z3,z190,z5]),(0,[z1,z2,z3,z7,z5,z157]),(0,[z1,z2,z866,z7,z40,z6]),(0,[z1,z2,z3,z7,z867,z6]),(0,[z1,z2,z3,z7,z868,z6])],[(0,[z1,z2,z869,z7,z5,z6]),(0,[z24,z77,z3,z7,z40,z6]),(0,[z1,z2,z3,z506,z5,z32]),(0,[z1,z2,z870,z3,z7,z6]),(0,[z1,z3,z7,z40,z331,z6]),(0,[z1,z2,z144,z375,z7,z6])],[(0,[z1,z2,z3,z871,z5,z6]),(0,[z1,z2,z16,z3,z7,z27]),(0,[z648,z212,z3,z7,z5,z6]),(0,[z1,z2,z872,z3,z7,z6]),(0,[z229,z587,z2,z3,z7,z5]),(0,[z873,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z874,z7,z5]),(0,[z1,z2,z14,z7,z202,z6])],[(0,[z1,z2,z3,z7,z5,z875]),(0,[z1,z2,z3,z39,z5,z152]),(0,[z876,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z877,z6]),(0,[z1,z2,z3,z168,z40,z32])],[(0,[z174,z2,z171,z66,z7,z6]),(0,[z10,z1,z16,z3,z70,z5]),(0,[z1,z2,z3,z7,z5,z878]),(0,[z1,z2,z3,z7,z879,z6]),(0,[z1,z2,z16,z3,z5,z678])],[(0,[z1,z2,z3,z7,z880,z6]),(0,[z1,z2,z3,z7,z881,z6]),(0,[z1,z2,z3,z7,z5,z882]),(0,[z1,z2,z3,z7,z5,z210])],[(0,[z1,z2,z883,z3,z5,z6]),(0,[z1,z2,z3,z7,z884,z6]),(0,[z1,z2,z3,z885,z5,z6]),(0,[z1,z2,z3,z4,z5,z152]),(0,[z1,z2,z3,z7,z5,z795]),(0,[z1,z2,z3,z7,z5,z886]),(0,[z1,z2,z3,z7,z887,z6])],[(0,[z1,z2,z593,z3,z5,z32]),(0,[z1,z2,z3,z482,z5,z32])]],
   [[(0,[z1,z2,z3,z329,z7,z40]),(0,[z1,z2,z888,z3,z7,z6])],[(0,[z1,z2,z3,z496,z7,z32]),(1,[z2,z3,z7,z5,z718]),(0,[z1,z2,z3,z7,z178,z6]),(0,[z1,z2,z889,z3,z7,z5]),(0,[z1,z15,z215,z3,z7,z5])],[(0,[z890,z1,z2,z3,z7,z5]),(0,[z1,z2,z891,z3,z7,z6]),(0,[z145,z2,z3,z7,z357,z6]),(0,[z1,z2,z3,z7,z20,z892]),(0,[z1,z323,z3,z7,z20,z6]),(0,[z1,z2,z3,z585,z5,z32]),(0,[z1,z721,z3,z7,z5,z32])],[(0,[z121,z2,z3,z4,z5,z6]),(0,[z230,z2,z3,z7,z5,z360]),(0,[z1,z2,z3,z7,z119,z6]),(0,[z1,z2,z316,z3,z5,z32]),(0,[z1,z2,z620,z76,z3,z6])],[(0,[z230,z2,z3,z7,z5,z6]),(0,[z53,z1,z3,z7,z20,z6])],[(0,[z1,z2,z3,z7,z5,z893]),(0,[z10,z1,z3,z767,z5,z6]),(0,[z370,z2,z3,z7,z569,z6])],[(0,[z1,z2,z894,z7,z5,z6]),(0,[z174,z2,z66,z7,z5,z32]),(0,[z1,z2,z895,z7,z5,z6]),(0,[z1,z2,z3,z7,z40,z345]),(0,[z1,z2,z114,z140,z7,z6])],[(1,[z801,z3,z7,z5,z6]),(0,[z1,z2,z3,z190,z5,z32]),(0,[z1,z2,z3,z7,z5,z896]),(0,[z1,z235,z3,z112,z5,z6]),(0,[z1,z2,z3,z168,z20,z32]),(0,[z1,z2,z71,z76,z3,z377]),(0,[z1,z2,z76,z3,z734,z6])]],
   [[(0,[z2,z3,z7,z40,z897,z6]),(0,[z196,z1,z3,z7,z5,z132]),(0,[z1,z2,z898,z3,z7,z5])],[(0,[z1,z2,z3,z7,z899,z5]),(0,[z1,z2,z3,z253,z7,z20]),(0,[z1,z392,z3,z7,z40,z6]),(0,[z1,z2,z214,z5,z52,z32])],[(0,[z1,z2,z900,z3,z7,z5]),(0,[z1,z2,z901,z7,z5,z6]),(0,[z1,z2,z902,z3,z5,z32]),(0,[z815,z2,z3,z7,z5,z6]),(0,[z1,z68,z758,z7,z5,z6]),(0,[z1,z2,z214,z5,z52,z275])],[(0,[z1,z2,z3,z903,z5,z6]),(0,[z1,z2,z3,z253,z7,z5]),(0,[z1,z2,z3,z7,z5,z904]),(0,[z1,z2,z3,z7,z213,z6]),(0,[z1,z2,z3,z7,z5,z905]),(0,[z10,z11,z3,z70,z5,z6]),(0,[z906,z2,z3,z7,z5,z6]),(0,[z1,z2,z907,z3,z7,z5]),(0,[z1,z2,z3,z7,z908,z6])],[(0,[z1,z2,z170,z16,z3,z7]),(0,[z61,z2,z3,z4,z40,z6]),(0,[z1,z3,z7,z767,z5,z6]),(0,[z1,z2,z3,z7,z909,z6]),(0,[z1,z910,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z911,z6]),(0,[z1,z2,z3,z7,z5,z912]),(0,[z1,z77,z3,z7,z442,z6]),(0,[z1,z2,z913,z3,z7,z6]),(0,[z1,z2,z3,z7,z5,z914]),(0,[z1,z2,z915,z7,z5,z6]),(0,[z2,z3,z716,z7,z5,z6]),(0,[z1,z3,z7,z40,z630,z6]),(0,[z1,z2,z16,z3,z916,z7])],[(0,[z1,z367,z3,z7,z40,z6]),(0,[z55,z212,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z917,z6])],[(0,[z94,z2,z95,z7,z5,z6]),(0,[z1,z2,z71,z3,z608,z6]),(0,[z177,z1,z69,z7,z20,z6]),(0,[z1,z2,z129,z744,z7,z5])]],
   [[(0,[z1,z2,z3,z7,z5,z32]),(0,[z1,z918,z3,z7,z5,z6]),(0,[z1,z2,z919,z3,z7,z6]),(0,[z218,z1,z2,z170,z3,z7]),(0,[z1,z2,z342,z7,z5,z32]),(0,[z1,z2,z3,z7,z40,z157]),(0,[z1,z2,z3,z7,z193,z133]),(0,[z1,z2,z16,z3,z7,z297]),(0,[z1,z2,z3,z7,z920,z6])],[(0,[z1,z399,z77,z3,z7,z40]),(0,[z1,z2,z3,z560,z5,z32]),(0,[z1,z2,z3,z221,z5,z32]),(0,[z701,z1,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z275]),(0,[z1,z2,z3,z7,z5,z921]),(1,[z1,z2,z757,z5,z6]),(0,[z1,z2,z16,z3,z7,z766])],[(0,[z1,z2,z3,z7,z922,z6]),(0,[z1,z2,z3,z7,z20,z345]),(0,[z51,z2,z3,z637,z7,z6]),(0,[z10,z230,z3,z70,z5,z6]),(0,[z1,z2,z3,z923,z7,z5])],[(0,[z11,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z924,z7,z5]),(0,[z11,z2,z342,z7,z5,z6]),(0,[z1,z664,z3,z7,z40,z6]),(0,[z1,z2,z7,z762,z5,z6]),(0,[z1,z2,z16,z3,z7,z909])],[(0,[z274,z77,z3,z7,z5,z6]),(0,[z230,z2,z3,z7,z539,z6]),(0,[z1,z2,z16,z3,z7,z753])],[(0,[z1,z2,z925,z7,z5,z6]),(0,[z1,z2,z3,z72,z695,z6]),(0,[z1,z2,z3,z7,z111,z6]),(0,[z1,z2,z342,z7,z111,z6]),(0,[z10,z1,z3,z70,z5,z32])],[(0,[z151,z77,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z926,z6]),(0,[z61,z2,z3,z4,z5,z152]),(0,[z1,z2,z548,z3,z190,z5]),(0,[z927,z1,z3,z7,z5,z6])],[(0,[z1,z2,z16,z3,z7,z379])]],
   [[(0,[z61,z2,z3,z4,z20,z6])],[(0,[z1,z2,z3,z7,z928,z6]),(0,[z1,z2,z214,z20,z52,z6]),(1,[z1,z2,z712,z3,z5]),(0,[z1,z2,z712,z3,z5,z6])],[(0,[z1,z2,z170,z3,z7,z6]),(0,[z1,z2,z3,z7,z5,z929]),(0,[z1,z367,z3,z7,z20,z6]),(0,[z1,z2,z14,z595,z7,z6]),(0,[z10,z1,z3,z70,z111,z6]),(0,[z1,z930,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z931,z32])],[(0,[z1,z932,z3,z7,z5,z6]),(0,[z1,z2,z933,z3,z7,z5]),(0,[z1,z2,z3,z934,z7,z6]),(0,[z1,z3,z7,z5,z727,z6]),(0,[z1,z2,z316,z3,z40,z32]),(0,[z1,z2,z3,z7,z5,z935]),(0,[z47,z1,z3,z7,z297,z132]),(0,[z2,z3,z7,z5,z728,z6])],[(0,[z1,z367,z114,z3,z7,z6]),(0,[z230,z2,z3,z7,z40,z6]),(0,[z230,z2,z3,z7,z5,z116]),(0,[z1,z2,z3,z7,z20,z157]),(0,[z1,z673,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z732,z6])],[(0,[z1,z3,z7,z5,z936,z6]),(0,[z1,z2,z3,z574,z5,z32]),(0,[z937,z1,z2,z3,z7,z40]),(0,[z1,z2,z214,z5,z210,z52])],[(0,[z229,z2,z3,z7,z5,z718]),(1,[z1,z2,z729,z3,z7])],[(0,[z1,z2,z16,z3,z7,z105]),(1,[z1,z758,z7,z5,z6]),(0,[z1,z2,z938,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z7,z539,z32]),(0,[z1,z578,z3,z7,z40,z6])],[(0,[z1,z2,z399,z3,z7,z20]),(0,[z1,z2,z3,z7,z5,z892]),(0,[z1,z2,z939,z3,z7,z6]),(0,[z1,z2,z3,z7,z940,z6]),(0,[z1,z2,z788,z7,z5,z6]),(0,[z1,z2,z391,z7,z202,z6]),(0,[z1,z2,z114,z30,z7,z32]),(0,[z1,z2,z38,z3,z160,z7])],[(0,[z1,z2,z729,z3,z7,z6])],[(0,[z1,z2,z866,z7,z5,z6]),(0,[z1,z2,z3,z7,z295,z32]),(0,[z1,z2,z941,z3,z7,z6]),(0,[z126,z2,z565,z3,z7,z6]),(0,[z942,z2,z3,z7,z5,z6]),(0,[z11,z2,z16,z3,z7,z5]),(0,[z11,z2,z3,z7,z539,z6]),(0,[z1,z2,z3,z903,z40,z6])],[(0,[z177,z1,z16,z69,z7,z5]),(0,[z1,z2,z3,z484,z5,z32])],[(0,[z1,z2,z943,z3,z7,z5]),(0,[z1,z2,z944,z7,z5,z6]),(0,[z1,z2,z28,z7,z5,z32]),(0,[z1,z2,z16,z3,z7,z231]),(0,[z1,z2,z3,z7,z20,z945]),(0,[z1,z3,z7,z5,z726,z162])],[(0,[z1,z2,z3,z168,z5,z32])],[(0,[z1,z2,z3,z7,z5,z946]),(0,[z1,z2,z947,z3,z7,z6]),(0,[z94,z2,z95,z7,z40,z6]),(1,[z2,z3,z7,z865,z6]),(0,[z1,z2,z3,z7,z20,z948]),(0,[z1,z2,z3,z7,z5,z949])]],
   [[(0,[z1,z2,z3,z7,z950,z6]),(0,[z951,z1,z2,z3,z7,z5]),(0,[z1,z2,z3,z7,z5,z952]),(0,[z55,z543,z3,z7,z5,z6]),(0,[z1,z2,z953,z3,z7,z5]),(0,[z126,z2,z3,z7,z8,z6]),(0,[z1,z2,z3,z558,z5,z32]),(0,[z11,z2,z28,z7,z5,z6]),(0,[z230,z2,z3,z7,z20,z6]),(0,[z1,z167,z3,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z954])],[(0,[z1,z2,z3,z7,z5,z955]),(0,[z1,z2,z3,z7,z297,z6])],[(0,[z1,z2,z956,z7,z5,z6]),(0,[z1,z2,z3,z957,z5,z6]),(0,[z1,z2,z28,z7,z111,z6])],[(0,[z1,z2,z3,z958,z7,z5]),(0,[z1,z2,z3,z7,z5,z959]),(0,[z1,z2,z214,z40,z52,z6]),(0,[z1,z118,z215,z3,z7,z5]),(0,[z960,z2,z3,z7,z5,z6])],[(0,[z961,z1,z2,z3,z7,z5]),(0,[z1,z2,z3,z534,z5,z32]),(0,[z1,z2,z3,z7,z722,z6]),(0,[z1,z2,z3,z7,z5,z962]),(0,[z1,z2,z744,z7,z5,z127]),(0,[z1,z2,z16,z3,z963,z7])],[(0,[z1,z77,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z964,z6]),(0,[z1,z2,z3,z388,z5,z32]),(0,[z1,z2,z3,z7,z965,z6]),(0,[z1,z2,z902,z3,z39,z5]),(0,[z1,z2,z3,z608,z5,z32]),(0,[z1,z2,z3,z696,z5,z32])],[(0,[z51,z2,z3,z7,z9,z6]),(0,[z177,z1,z69,z7,z5,z6]),(0,[z1,z2,z3,z7,z377,z40]),(0,[z1,z2,z3,z329,z7,z20]),(0,[z1,z2,z71,z16,z76,z3])],[(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z497,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z967,z32])]],
   [[(0,[z1,z2,z3,z7,z327,z32]),(0,[z1,z2,z3,z7,z968,z6]),(0,[z1,z2,z16,z3,z7,z111]),(0,[z1,z118,z3,z7,z40,z162]),(0,[z1,z2,z3,z744,z7,z5])],[(0,[z1,z2,z969,z3,z5,z6]),(0,[z24,z2,z3,z430,z5,z6]),(0,[z1,z2,z89,z3,z7,z32]),(0,[z1,z2,z3,z7,z970,z6])],[(0,[z971,z1,z2,z3,z7,z5]),(0,[z1,z2,z3,z972,z7,z5]),(0,[z1,z96,z16,z3,z7,z5]),(0,[z1,z2,z3,z7,z973,z6])],[(0,[z186,z325,z77,z3,z7,z5]),(0,[z1,z2,z3,z974,z7,z5]),(0,[z1,z2,z758,z7,z5,z6]),(0,[z1,z2,z3,z7,z40,z935]),(0,[z1,z2,z620,z259,z3,z6]),(0,[z1,z771,z3,z7,z5,z6]),(0,[z294,z1,z2,z349,z3,z7])],[(0,[z1,z2,z71,z76,z3,z103])],[(0,[z1,z212,z3,z7,z442,z6]),(0,[z1,z975,z2,z3,z7,z5]),(0,[z1,z2,z3,z7,z976,z6]),(0,[z2,z95,z788,z7,z5,z6]),(0,[z1,z2,z3,z7,z977,z6])],[(0,[z1,z704,z3,z7,z40,z6]),(0,[z1,z3,z7,z20,z535,z6]),(0,[z1,z2,z129,z3,z190,z5]),(0,[z1,z19,z68,z7,z213,z6]),(0,[z1,z2,z16,z3,z7,z363]),(0,[z1,z2,z978,z3,z7,z20]),(0,[z1,z2,z3,z7,z379,z32])],[(0,[z1,z2,z3,z7,z979,z6]),(0,[z61,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z7,z980,z6])],[(0,[z1,z367,z3,z7,z5,z6]),(0,[z218,z1,z2,z3,z7,z40]),(0,[z1,z2,z981,z3,z7,z5]),(0,[z982,z2,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z477,z5])],[(0,[z1,z2,z3,z7,z5,z983]),(0,[z1,z2,z3,z984,z5,z6]),(0,[z0,z1,z2,z16,z3,z40]),(0,[z1,z2,z3,z7,z193,z115])],[(0,[z174,z2,z253,z66,z7,z5]),(0,[z1,z2,z3,z7,z985,z6]),(0,[z1,z19,z68,z7,z5,z32]),(0,[z1,z2,z986,z7,z5,z6]),(0,[z1,z195,z3,z7,z743,z6]),(0,[z1,z2,z3,z7,z786,z6])],[(0,[z1,z2,z3,z7,z987,z5]),(0,[z1,z2,z988,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z989]),(0,[z1,z2,z3,z484,z40,z32]),(0,[z1,z118,z3,z7,z20,z162]),(0,[z63,z2,z3,z7,z5,z81])],[(0,[z174,z2,z16,z66,z7,z5]),(0,[z1,z2,z3,z7,z5,z990]),(0,[z1,z2,z3,z108,z7,z40])],[(0,[z1,z2,z991,z7,z5,z6]),(0,[z1,z992,z3,z7,z5,z6]),(0,[z61,z2,z3,z496,z4,z6]),(0,[z1,z2,z3,z7,z993,z6])],[(0,[z1,z2,z3,z994,z7,z6]),(0,[z1,z2,z995,z3,z7,z6]),(0,[z1,z2,z996,z3,z7,z6]),(0,[z1,z2,z431,z3,z221,z5]),(0,[z1,z2,z997,z7,z5,z6]),(0,[z1,z2,z3,z7,z347,z6]),(0,[z998,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z72,z513,z6])]],
   [[(0,[z1,z2,z3,z7,z40,z952]),(0,[z1,z2,z799,z3,z7,z6])],[(0,[z151,z77,z3,z7,z5,z6]),(0,[z51,z2,z3,z7,z357,z6]),(0,[z1,z2,z999,z7,z5,z6]),(1,[z1,z3,z767,z5,z6]),(0,[z47,z1,z3,z7,z40,z132]),(0,[z1,z2,z3,z7,z1000,z6])],[(0,[z1,z2,z3,z7,z1001,z6]),(0,[z1,z2,z956,z7,z40,z6]),(0,[z99,z1,z2,z124,z7,z40]),(0,[z206,z1,z3,z7,z20,z32])],[(0,[z1,z2,z3,z7,z719,z32])],[(0,[z1,z2,z3,z7,z40,z962]),(0,[z1,z2,z3,z7,z5,z945]),(0,[z31,z1,z2,z136,z3,z7]),(0,[z1,z2,z3,z481,z5,z32])],[(0,[z1,z2,z3,z1002,z5,z6]),(0,[z1,z367,z71,z3,z7,z6]),(0,[z1,z2,z7,z757,z5,z6]),(0,[z1,z1003,z3,z7,z5,z6]),(0,[z1,z2,z114,z7,z762,z6]),(0,[z1,z2,z260,z16,z3,z5])],[(0,[z2,z788,z66,z7,z5,z6]),(0,[z177,z1,z69,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z948])],[(0,[z1,z2,z3,z1004,z7,z5]),(0,[z1,z1005,z3,z7,z5,z6]),(0,[z1,z2,z431,z3,z7,z40]),(0,[z1,z2,z3,z7,z5,z1006]),(0,[z1,z367,z3,z7,z9,z6]),(0,[z1,z2,z3,z1007,z5,z6]),(0,[z1,z2,z3,z7,z1008,z6]),(0,[z230,z2,z342,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z7,z27,z6]),(0,[z1,z2,z1009,z7,z5,z6]),(0,[z1,z212,z3,z7,z1001,z6]),(0,[z126,z2,z3,z7,z569,z6]),(0,[z1,z2,z3,z532,z5,z32])],[(0,[z1,z2,z171,z3,z7,z6]),(0,[z1,z367,z16,z3,z7,z5]),(0,[z1,z2,z16,z3,z7,z539]),(0,[z1,z2,z1010,z3,z7,z5]),(0,[z113,z1,z2,z16,z3,z5]),(0,[z1,z2,z3,z1011,z5,z6])],[(0,[z77,z3,z7,z4,z40,z6]),(0,[z1,z2,z3,z7,z1012,z6])],[],[(0,[z1,z2,z3,z7,z5,z1013]),(0,[z1,z3,z7,z743,z40,z6])],[(0,[z937,z1,z2,z3,z7,z5]),(0,[z1,z2,z142,z3,z7,z40]),(0,[z1,z2,z14,z7,z202,z32]),(0,[z1,z2,z124,z744,z7,z5])],[(0,[z99,z1,z2,z555,z7,z5]),(0,[z1,z2,z3,z7,z40,z360]),(0,[z1014,z1,z2,z3,z7,z5]),(0,[z1,z2,z1015,z3,z40,z6]),(0,[z1,z2,z3,z7,z40,z305])],[(0,[z1,z2,z3,z7,z40,z6]),(0,[z1,z2,z1016,z3,z7,z6]),(0,[z1017,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z116]),(0,[z1,z92,z3,z7,z40,z6]),(0,[z1,z2,z16,z3,z385,z5])]],
   [[(1,[z2,z788,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z1018]),(0,[z1,z2,z3,z221,z40,z6]),(0,[z508,z1,z2,z38,z3,z7]),(0,[z1,z1019,z3,z7,z5,z6])],[(0,[z55,z212,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z831,z6]),(0,[z1,z2,z187,z109,z5,z32]),(0,[z1,z2,z3,z734,z6,z138])],[(0,[z1,z2,z3,z209,z5,z32]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z74,z1,z2,z16,z3,z5]),(0,[z1,z2,z3,z7,z1021,z6]),(0,[z1,z235,z142,z3,z112,z5]),(0,[z1,z2,z3,z7,z5,z1022]),(0,[z1,z2,z129,z234,z7,z5]),(0,[z1,z2,z163,z234,z7,z5])],[(0,[z1,z2,z902,z3,z7,z5]),(0,[z1,z2,z3,z688,z5,z32]),(0,[z1,z2,z16,z3,z575,z5])],[(0,[z186,z77,z3,z7,z5,z32]),(0,[z94,z2,z788,z7,z5,z6])],[(0,[z1,z212,z3,z7,z40,z6]),(0,[z2,z77,z3,z4,z5,z32]),(0,[z1,z2,z3,z1023,z5,z6]),(0,[z1,z2,z3,z695,z5,z32]),(0,[z2,z3,z7,z5,z718,z6]),(0,[z42,z2,z268,z3,z7,z5]),(0,[z1,z2,z3,z767,z5,z6]),(0,[z1,z2,z384,z340,z7,z6]),(0,[z1,z2,z3,z7,z223,z115])],[(0,[z55,z801,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z1024]),(0,[z1025,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z231,z32]),(0,[z1,z2,z3,z7,z1026,z20])],[(0,[z1,z2,z3,z7,z1027,z6]),(0,[z1,z2,z407,z3,z5,z32]),(0,[z230,z2,z16,z3,z7,z5])]],
   [[(0,[z325,z1,z2,z3,z7,z40]),(0,[z1,z2,z3,z7,z1026,z5]),(0,[z1,z2,z3,z7,z1028,z6]),(0,[z1,z2,z759,z3,z7,z32])],[(0,[z1,z2,z3,z7,z5,z152]),(0,[z1,z2,z187,z108,z109,z5])],[(0,[z1,z2,z3,z7,z5,z1029]),(0,[z1,z2,z3,z7,z20,z360]),(0,[z1,z195,z3,z7,z40,z6]),(0,[z1,z2,z16,z3,z7,z40]),(0,[z1,z2,z3,z7,z20,z305]),(0,[z1,z2,z3,z7,z20,z1030]),(0,[z1,z2,z3,z7,z1031,z6])],[(0,[z1,z2,z3,z7,z20,z6]),(0,[z212,z801,z3,z7,z5,z6]),(0,[z1,z2,z16,z3,z7,z295]),(0,[z1,z2,z3,z7,z5,z1032]),(0,[z1,z118,z3,z7,z5,z162]),(0,[z2,z3,z7,z5,z1033,z6])],[(0,[z24,z2,z3,z39,z5,z345]),(0,[z1,z2,z3,z221,z20,z6]),(0,[z230,z2,z28,z7,z5,z6]),(0,[z1,z235,z3,z767,z5,z6]),(0,[z1,z436,z2,z287,z7,z5])],[(0,[z1,z2,z71,z76,z3,z32])],[(0,[z1,z1034,z3,z7,z5,z6]),(0,[z1,z2,z1035,z3,z7,z5]),(0,[z1,z2,z3,z7,z213,z32]),(0,[z1,z2,z3,z916,z7,z6]),(0,[z1,z2,z3,z7,z377,z5])],[(0,[z1,z1036,z2,z3,z7,z5]),(0,[z42,z2,z3,z7,z5,z246]),(0,[z1,z2,z16,z28,z7,z5]),(0,[z1,z2,z3,z7,z539,z116]),(1,[z1,z3,z7,z743,z6]),(0,[z1,z3,z7,z5,z770,z32]),(0,[z1,z910,z3,z7,z5,z32])]],
   [[(0,[z1,z212,z16,z3,z7,z40]),(0,[z24,z2,z431,z3,z39,z5]),(0,[z42,z2,z3,z221,z5,z246]),(0,[z1,z2,z3,z7,z409,z115]),(0,[z1,z2,z16,z3,z7,z29]),(0,[z1,z2,z3,z7,z1037,z6])],[(0,[z1,z2,z3,z7,z1038,z6]),(0,[z1,z2,z3,z7,z5,z1039]),(0,[z1,z19,z68,z7,z363,z6]),(0,[z1,z2,z3,z1040,z5,z6])],[(0,[z1,z2,z3,z7,z5,z1041]),(0,[z1,z2,z141,z7,z309,z6]),(0,[z1,z2,z3,z7,z5,z1042]),(0,[z121,z2,z3,z7,z5,z159])],[(0,[z1,z2,z3,z584,z5,z32]),(0,[z1,z2,z16,z3,z5,z252]),(0,[z1,z2,z3,z7,z5,z1043]),(0,[z1,z2,z3,z7,z1044,z6]),(0,[z1,z2,z16,z3,z7,z836])],[(0,[z1,z2,z3,z7,z5,z1045]),(0,[z1,z2,z7,z762,z202,z6])],[(0,[z1,z2,z1046,z3,z7,z5]),(0,[z1,z2,z3,z1047,z7,z5]),(0,[z1,z195,z16,z3,z7,z40])],[(0,[z1,z2,z399,z3,z7,z5]),(0,[z1,z607,z3,z7,z40,z6]),(0,[z1,z367,z3,z7,z8,z6]),(0,[z42,z2,z33,z3,z7,z5]),(0,[z11,z2,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z5,z1048]),(0,[z1,z2,z14,z7,z762,z6])],[(0,[z1,z2,z3,z7,z1049,z6]),(0,[z218,z1,z2,z3,z7,z20]),(0,[z296,z2,z3,z7,z8,z6]),(0,[z1,z2,z3,z7,z40,z116])]],
   [[(0,[z1,z2,z3,z7,z1050,z6]),(0,[z0,z1,z2,z16,z3,z20]),(0,[z1,z2,z3,z7,z29,z32])],[(0,[z218,z1,z2,z3,z7,z5]),(0,[z1,z3,z7,z5,z132,z726])],[(0,[z1,z2,z3,z7,z1051,z6]),(0,[z1,z2,z3,z7,z1052,z6])],[(0,[z1,z2,z3,z496,z7,z6]),(0,[z1,z2,z3,z7,z1053,z6]),(0,[z11,z2,z3,z7,z111,z6]),(0,[z1,z2,z1054,z7,z5,z6]),(0,[z494,z1,z3,z7,z40,z6]),(0,[z1,z2,z3,z108,z7,z20])],[(0,[z1,z1055,z3,z7,z5,z6]),(0,[z47,z1,z3,z7,z5,z132])],[(0,[z1,z3,z7,z20,z40,z32]),(0,[z1,z2,z3,z108,z7,z5])],[(0,[z1,z2,z3,z7,z5,z1056]),(0,[z1,z243,z3,z7,z40,z6]),(0,[z2,z3,z7,z865,z9,z6]),(0,[z1,z631,z3,z7,z40,z6]),(0,[z1,z2,z3,z627,z5,z32]),(0,[z1,z2,z3,z734,z5,z6])],[(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1,z2,z3,z1058,z7,z6]),(0,[z1,z2,z3,z39,z5,z32]),(0,[z229,z197,z2,z3,z7,z5]),(0,[z1,z2,z391,z7,z428,z6])]],
   [[(0,[z1,z3,z7,z22,z40,z6]),(0,[z1,z2,z3,z7,z5,z1059]),(0,[z99,z1,z2,z124,z7,z20])],[(0,[z1,z2,z3,z125,z5,z32]),(0,[z1,z2,z3,z7,z40,z152]),(0,[z1,z2,z3,z190,z5,z6]),(0,[z1,z2,z431,z3,z5,z32]),(0,[z1,z2,z3,z7,z1060,z6])],[(0,[z1,z2,z3,z7,z442,z6]),(0,[z1,z3,z7,z295,z40,z6]),(0,[z1,z2,z3,z4,z5,z32])],[(0,[z186,z77,z3,z7,z442,z6]),(0,[z1,z2,z3,z7,z20,z116]),(0,[z1,z2,z3,z7,z743,z6]),(0,[z1,z3,z7,z357,z40,z6]),(0,[z1,z2,z166,z316,z3,z6]),(0,[z1,z2,z14,z7,z309,z6]),(0,[z1,z2,z214,z5,z52,z6]),(0,[z1,z2,z3,z329,z7,z5])],[(0,[z1,z2,z3,z7,z1061,z6]),(0,[z1,z2,z3,z7,z1062,z5]),(0,[z1,z2,z3,z7,z1063,z6]),(0,[z1,z2,z445,z3,z5,z32])],[(0,[z1,z2,z431,z3,z7,z20]),(0,[z1,z96,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z1064,z6]),(0,[z1,z476,z68,z7,z5,z6]),(0,[z1,z16,z3,z7,z20,z40])],[(0,[z1,z2,z1065,z3,z7,z6]),(0,[z1,z2,z3,z7,z5,z1066])],[(0,[z1,z2,z431,z3,z7,z5]),(0,[z42,z2,z3,z7,z40,z246]),(0,[z1,z3,z7,z743,z5,z6]),(0,[z1,z2,z3,z7,z1067,z6])]],
   [[(0,[z1,z2,z3,z7,z105,z32]),(0,[z1,z2,z3,z7,z1068,z5])],[(0,[z1,z2,z1015,z3,z5,z6]),(0,[z1,z367,z3,z7,z22,z6]),(0,[z126,z2,z3,z7,z865,z6]),(0,[z1,z2,z3,z1069,z5,z6]),(0,[z1,z2,z3,z7,z5,z1030]),(0,[z1,z2,z3,z7,z5,z360]),(0,[z1,z2,z342,z7,z5,z360]),(0,[z1,z2,z3,z1040,z40,z6]),(0,[z1,z3,z629,z7,z20,z6]),(0,[z1,z2,z3,z7,z5,z305]),(0,[z1,z2,z3,z7,z1070,z5]),(0,[z1,z2,z729,z3,z7,z5])],[(0,[z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z963,z7,z6]),(0,[z1,z1071,z3,z7,z5,z6]),(0,[z1,z2,z342,z7,z5,z6]),(0,[z1,z2,z3,z7,z1072,z6]),(0,[z1,z19,z68,z7,z40,z6]),(0,[z296,z2,z3,z7,z22,z6]),(0,[z1,z2,z3,z7,z762,z6]),(0,[z1,z2,z3,z7,z193,z65])],[(0,[z1,z2,z1073,z7,z5,z6]),(0,[z1,z2,z978,z3,z7,z5]),(0,[z1,z2,z3,z221,z5,z6]),(0,[z1,z2,z3,z165,z5,z32]),(0,[z1,z2,z1074,z3,z7,z5]),(0,[z1,z2,z142,z3,z7,z20])],[(0,[z1,z2,z3,z7,z5,z1075]),(0,[z1,z2,z1076,z7,z5,z6]),(0,[z1,z659,z3,z7,z40,z6]),(0,[z1,z2,z114,z340,z7,z6])],[(0,[z1,z1077,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z1078]),(0,[z1,z2,z3,z7,z20,z152]),(0,[z1,z2,z3,z7,z5,z1079]),(0,[z1,z2,z3,z638,z5,z32])],[(0,[z1,z2,z3,z7,z5,z1080]),(0,[z1,z2,z171,z16,z3,z7]),(0,[z1,z2,z3,z716,z5,z6]),(0,[z24,z2,z3,z39,z5,z32]),(0,[z10,z1,z3,z70,z5,z360]),(0,[z1,z2,z1081,z3,z7,z6]),(0,[z1,z2,z3,z1082,z7,z5])],[(0,[z1,z2,z16,z3,z7,z327]),(0,[z10,z1,z3,z70,z5,z6]),(0,[z1,z292,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z844,z40]),(0,[z508,z1,z2,z100,z3,z7])]],
   [[(0,[z1,z77,z3,z7,z40,z32]),(0,[z1,z2,z170,z3,z253,z7]),(0,[z1,z367,z14,z3,z7,z6]),(0,[z1083,z2,z3,z7,z5,z6]),(0,[z1,z2,z1084,z3,z7,z5]),(0,[z1,z834,z3,z7,z5,z32])],[(0,[z186,z801,z3,z7,z5,z6]),(0,[z206,z1,z3,z7,z743,z6]),(0,[z1,z118,z3,z7,z379,z162]),(0,[z196,z1,z603,z3,z7,z5])],[(0,[z1,z2,z1085,z7,z5,z6]),(0,[z1,z2,z3,z7,z1086,z6]),(1,[z1,z2,z744,z7,z5])],[(0,[z1,z2,z3,z7,z5,z1087]),(0,[z42,z2,z3,z7,z20,z246]),(0,[z1,z2,z16,z3,z5,z668]),(0,[z1,z2,z3,z650,z5,z32])],[(0,[z1088,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z1089,z6]),(0,[z1,z2,z16,z3,z5,z32]),(0,[z1,z2,z3,z7,z931,z6])],[(0,[z1,z2,z3,z7,z5,z1090]),(0,[z1,z2,z3,z180,z5,z32]),(0,[z1,z235,z3,z112,z5,z157]),(0,[z1,z2,z33,z3,z5,z32]),(0,[z31,z1,z2,z38,z3,z7])],[(0,[z325,z1,z2,z3,z7,z20]),(0,[z1,z2,z3,z1091,z5,z6]),(0,[z61,z2,z3,z4,z5,z562]),(0,[z1,z19,z68,z7,z20,z6])],[(0,[z1,z2,z1092,z7,z5,z6]),(0,[z1,z2,z3,z39,z40,z32]),(0,[z494,z1,z69,z7,z5,z6]),(0,[z1,z2,z3,z874,z7,z40])]],
   [[(0,[z325,z1,z2,z3,z7,z5]),(0,[z1093,z1,z2,z3,z7,z5]),(0,[z174,z2,z66,z7,z40,z6]),(0,[z1,z2,z3,z7,z1094,z5]),(0,[z229,z2,z3,z7,z5,z81]),(0,[z1,z2,z16,z3,z7,z20]),(0,[z1,z2,z287,z124,z7,z5]),(0,[z1,z2,z3,z329,z72,z138])],[(0,[z1,z2,z3,z211,z5,z32]),(0,[z1,z2,z3,z190,z40,z6]),(0,[z1,z2,z3,z7,z363,z32]),(0,[z1,z2,z3,z7,z539,z360]),(0,[z1,z2,z1095,z7,z5,z6]),(0,[z1,z454,z3,z7,z40,z6]),(1,[z1,z2,z7,z762,z6])],[(0,[z1,z2,z3,z4,z40,z32]),(0,[z47,z1,z84,z3,z7,z5]),(0,[z1,z2,z3,z7,z539,z6]),(0,[z1,z2,z342,z7,z539,z6]),(0,[z1,z2,z129,z7,z5,z127])],[(0,[z1,z2,z3,z7,z1096,z6]),(0,[z218,z1,z2,z171,z3,z7]),(0,[z1,z3,z663,z7,z20,z6]),(0,[z1,z2,z114,z30,z7,z6])],[(0,[z186,z77,z3,z7,z27,z6]),(0,[z1,z367,z3,z7,z5,z32]),(0,[z1,z2,z3,z7,z5,z1097]),(0,[z1,z690,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z1098]),(0,[z1,z2,z16,z3,z5,z319]),(0,[z1,z2,z693,z16,z3,z5])],[(0,[z1,z2,z3,z7,z295,z6]),(0,[z618,z2,z3,z4,z5,z6]),(0,[z24,z2,z3,z716,z5,z6]),(0,[z1,z2,z1099,z3,z7,z5]),(0,[z1,z2,z3,z7,z5,z1100]),(0,[z1,z2,z1101,z7,z5,z6]),(0,[z1,z335,z3,z7,z40,z6]),(0,[z817,z2,z3,z7,z5,z6])],[(0,[z1,z2,z16,z3,z496,z7]),(0,[z126,z2,z418,z3,z7,z6]),(0,[z1,z2,z28,z7,z5,z360]),(0,[z99,z1,z2,z320,z7,z5])],[(0,[z1,z2,z3,z7,z5,z1102]),(0,[z1,z2,z28,z7,z5,z6]),(0,[z10,z1,z3,z70,z539,z6]),(0,[z1,z3,z7,z40,z331,z32]),(0,[z1,z2,z71,z316,z3,z6])]],
   [[(0,[z1103,z1,z2,z3,z7,z5]),(0,[z1,z235,z3,z112,z231,z6]),(0,[z1,z2,z187,z109,z40,z6])],[(0,[z1,z2,z1104,z7,z5,z6]),(0,[z1105,z2,z3,z7,z5,z6]),(0,[z151,z2,z3,z7,z272,z6])],[(0,[z1,z2,z3,z7,z5,z1106]),(0,[z1,z2,z342,z7,z40,z6]),(0,[z1,z2,z342,z7,z5,z116]),(0,[z31,z1,z2,z729,z3,z7])],[(0,[z186,z77,z3,z7,z40,z6]),(0,[z174,z218,z2,z66,z7,z5]),(0,[z1,z2,z3,z39,z20,z32]),(0,[z51,z96,z3,z7,z9,z6]),(0,[z2,z3,z7,z5,z897,z6]),(0,[z1,z681,z3,z7,z20,z6])],[(0,[z174,z2,z66,z7,z20,z6]),(0,[z1,z2,z3,z7,z1107,z6]),(0,[z1,z2,z3,z7,z1108,z6]),(0,[z1,z2,z3,z7,z1109,z6])],[(0,[z1,z2,z3,z7,z5,z1110]),(0,[z1,z2,z3,z190,z20,z6]),(0,[z1,z2,z16,z3,z221,z5])],[(0,[z1,z2,z1111,z3,z7,z6]),(0,[z61,z2,z3,z716,z5,z6]),(0,[z1,z2,z3,z4,z20,z32]),(0,[z177,z1,z69,z7,z105,z6]),(0,[z1,z19,z758,z7,z5,z6]),(0,[z1112,z2,z3,z7,z5,z6]),(0,[z1,z343,z3,z7,z40,z6])],[(0,[z1,z2,z1113,z3,z7,z6]),(0,[z1,z2,z3,z7,z1114,z6]),(0,[z1,z2,z3,z7,z178,z32]),(0,[z1115,z2,z3,z7,z5,z6]),(0,[z10,z1,z3,z70,z5,z116]),(0,[z10,z1,z3,z70,z40,z6]),(0,[z1,z35,z3,z7,z40,z6]),(0,[z1,z2,z712,z3,z168,z5]),(0,[z0,z1,z2,z712,z3,z5])]],
   [[(0,[z1,z380,z3,z7,z40,z6]),(0,[z1,z2,z3,z7,z5,z1116])],[(0,[z1,z2,z3,z7,z5,z1117]),(0,[z1,z3,z7,z1001,z40,z6]),(0,[z121,z2,z3,z4,z5,z32]),(0,[z1,z2,z3,z7,z967,z6]),(0,[z42,z2,z3,z190,z5,z246]),(0,[z1,z2,z3,z7,z550,z133]),(0,[z1,z2,z3,z7,z119,z32])],[(0,[z1,z2,z3,z7,z327,z6]),(0,[z1,z2,z3,z7,z1118,z6]),(0,[z2,z3,z788,z7,z5,z6]),(0,[z2,z3,z7,z8,z865,z6]),(0,[z230,z2,z3,z7,z5,z32]),(0,[z772,z1,z2,z3,z7,z40]),(0,[z1,z2,z3,z699,z5,z32])],[(0,[z206,z1,z3,z7,z295,z6]),(0,[z1,z2,z3,z7,z5,z1119]),(0,[z1,z2,z3,z7,z20,z377]),(0,[z1,z2,z3,z734,z72,z6])],[(0,[z1,z2,z3,z7,z1120,z6]),(0,[z1,z2,z3,z7,z1121,z6]),(0,[z2,z3,z7,z5,z865,z6]),(0,[z1,z2,z16,z3,z40,z32]),(0,[z1,z2,z187,z109,z20,z6]),(0,[z26,z1,z2,z136,z3,z7]),(0,[z1,z2,z144,z30,z7,z6]),(0,[z1,z2,z895,z7,z5,z32])],[(0,[z1,z2,z3,z7,z1122,z6]),(0,[z1,z2,z131,z3,z5,z32]),(0,[z1,z235,z3,z112,z5,z32]),(0,[z1,z2,z187,z757,z5,z6])],[(0,[z1,z2,z3,z7,z1123,z6]),(0,[z1,z2,z3,z7,z40,z562]),(0,[z51,z2,z3,z7,z865,z6]),(0,[z1,z2,z342,z7,z20,z6]),(0,[z1,z2,z3,z7,z20,z1068])],[(0,[z186,z77,z3,z7,z20,z6]),(0,[z1,z2,z1124,z3,z7,z6]),(0,[z1,z2,z3,z741,z5,z6]),(0,[z230,z2,z3,z7,z111,z6]),(0,[z1,z2,z28,z7,z539,z6]),(0,[z1,z2,z1125,z3,z7,z5]),(0,[z1,z2,z757,z5,z52,z6]),(0,[z1,z2,z14,z16,z7,z202]),(0,[z1,z2,z16,z3,z72,z138])]],
   [[(0,[z1,z2,z3,z7,z1126,z6]),(0,[z61,z2,z16,z3,z4,z5]),(0,[z1,z2,z3,z7,z379,z6]),(0,[z1,z3,z7,z20,z511,z6]),(0,[z1,z2,z901,z7,z5,z32])],[(0,[z1,z2,z1127,z7,z5,z6]),(0,[z1,z84,z3,z7,z40,z6])],[(0,[z1,z88,z3,z7,z40,z6]),(0,[z1,z2,z548,z3,z5,z32]),(0,[z1,z367,z3,z72,z7,z6]),(0,[z1,z2,z3,z7,z1128,z6]),(0,[z2,z3,z7,z5,z718,z246]),(0,[z1129,z2,z3,z7,z5,z6]),(0,[z1,z2,z129,z7,z40,z127]),(0,[z361,z1,z2,z3,z160,z7])],[(0,[z1,z1130,z3,z7,z5,z6]),(0,[z1,z2,z187,z308,z5,z6]),(0,[z10,z1,z3,z70,z20,z6]),(0,[z1,z2,z3,z7,z409,z172]),(0,[z1,z2,z3,z7,z5,z130])],[(0,[z1,z2,z3,z7,z5,z1131]),(0,[z1,z2,z3,z7,z5,z1132]),(0,[z1133,z1,z2,z3,z7,z5]),(0,[z1,z2,z3,z1134,z5,z6]),(0,[z1,z2,z3,z7,z1135,z6]),(0,[z1,z2,z3,z7,z5,z103]),(0,[z1,z2,z16,z3,z7,z777])],[(0,[z94,z2,z95,z7,z5,z32]),(0,[z1,z2,z1136,z3,z7,z6]),(0,[z1,z19,z68,z7,z5,z6])],[(0,[z1,z2,z3,z1137,z5,z6]),(0,[z1138,z1,z2,z3,z7,z5]),(0,[z1,z2,z3,z708,z7,z20])],[(0,[z1,z2,z1139,z3,z7,z6]),(0,[z1,z1140,z3,z7,z5,z6]),(0,[z1,z3,z758,z7,z5,z6]),(0,[z1,z2,z28,z7,z40,z6]),(0,[z1,z2,z28,z7,z5,z116]),(0,[z1141,z1,z2,z3,z7,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 528).take 520) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1048).take 254) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1302)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [528, 520, 254] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 114).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 226).take 30).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [114, 112, 30] = true :=
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

end PEqualNP.Outside.L_meta_43588

theorem PEqualNP.Outside.L_meta_43588 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4271959168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4271959168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43588.solve