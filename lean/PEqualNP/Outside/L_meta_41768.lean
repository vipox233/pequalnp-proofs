import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41768

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
  Nat.testBit (4276677312 * 2 ^ 32 + 3941132800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00046c578061b854#64 ++ 0x00011b15e0186e15#64 ++ 0xe00cfcff83e3f8fe#64 ++ 0xf8033f3fe0f8fe3f#64 : BitVec 256),
   (0x10711531b52c5b30#64 ++ 0x041c454c6d4b16cc#64 ++ 0xf0f31f33fd3c7f33#64 ++ 0x7c3cc7ccff4f1fcc#64 : BitVec 256),
   (0x8702a2c2da368dc0#64 ++ 0x21c0a8b0b68da370#64 ++ 0xff03e3c3fe3f8fc3#64 ++ 0xbfc0f8f0ff8fe3f0#64 : BitVec 256),
   (0x2bb803a80f8006a8#64 ++ 0x4aee00ea03e001aa#64 ++ 0xbffc03fc0fc00fff#64 ++ 0xefff00ff03f003ff#64 : BitVec 256),
   (0x4ddfd8000fdb6000#64 ++ 0x9377f60003f6d800#64 ++ 0xdffffc000ffff003#64 ++ 0xf7ffff0003fffc00#64 : BitVec 256),
   (0x6eefffff60000001#64 ++ 0x1bbbffffd8000000#64 ++ 0x6ffffffff0000003#64 ++ 0xdbfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 4]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0xe00cfcff83e3f8fe 0xf8033f3fe0f8fe3f

def z1 : W := mkw 0x10000411b0241910 0x040001046c090644 0x00000003f0000000 0x00000000fc000000

def z2 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0f31f33fd3c7f33 0x7c3cc7ccff4f1fcc

def z3 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0xbffc03fc0fc00fff 0xefff00ff03f003ff

def z4 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xdffffc000ffff003 0xf7ffff0003fffc00

def z5 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x6ffffffff0000003 0xdbfffffffc000000

def z6 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff03e3c3fe3f8fc3 0xbfc0f8f0ff8fe3f0

def z7 : W := mkw 0x4ddfd8009fff6900 0x9377f60027ffda40 0xffffff03ffffff03 0xffffffc0ffffffc0

def z8 : W := mkw 0xafba83a85f9607a8 0x6beea0ea17e581ea 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z9 : W := mkw 0x050280000a120000 0x0140a00002848000 0xdf03e0000e3f8003 0xb7c0f800038fe000

def z10 : W := mkw 0xcfdffac2dfffedc0 0xb3f7feb0b7fffb70 0xffffffc3ffffffc3 0xfffffff0fffffff0

def z11 : W := mkw 0x0602a2c240000000 0x0180a8b090000000 0x6f03e3c3f0000003 0x9bc0f8f0fc000000

def z12 : W := mkw 0x6eeb93a860000001 0x1bbae4ea18000000 0x0ff3030070000001 0x03fcc0c01c000000

def z13 : W := mkw 0x000468460041a044 0x00011a1180106811 0xc00cfccc03e3f0ce 0xf0033f3300f8fc33

def z14 : W := mkw 0x4cdfd80005084000 0x1337f60001421000 0xdffffc000d3c7003 0xf7ffff00034f1c00

def z15 : W := mkw 0x011000000fdb6000 0x8044000003f6d800 0x900000000ffff000 0x2400000003fffc00

def z16 : W := mkw 0xcfdb92805f9e4580 0xb3f6e4a017e79160 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z17 : W := mkw 0x8706eed7da368dc0 0x21c1bbb5f68da370 0xff0ffffffe3f8fc3 0xffc3ffffff8fe3f0

def z18 : W := mkw 0x10411411b02c5910 0x041045046c0b1644 0x40031c03f03c7000 0x1000c700fc0f1c00

def z19 : W := mkw 0x2b8802880a800488 0x4ae200a202a00122 0x0f0c00cc02c000cc 0x83c3003300b00033

def z20 : W := mkw 0x0051100005084000 0x0014440001421000 0xd0f31c000d3c7003 0x743cc700034f1c00

def z21 : W := mkw 0x6e8eeace40000001 0x1ba3bab390000000 0x0f0ce0cc00000000 0x83c3383300000000

def z22 : W := mkw 0x3bf917b92f8856b8 0x4efe45ee4be215ae 0xbffc1ffc0fc07fff 0xefff07ff03f01fff

def z23 : W := mkw 0x00046c5700000000 0x00011b15c0000000 0xe00cfcff83c008fe 0xf8033f3fe0f0023f

def z24 : W := mkw 0x0000245780209854 0x00000915e0082615 0x200000ff800008fc 0x0800003fe000023f

def z25 : W := mkw 0x4ddffc578ffbf854 0x9377ff15e3fefe15 0xfffffcff8ffff8ff 0xffffff3fe3fffe3f

def z26 : W := mkw 0xef8eeaceda368dc1 0x3be3bab3b68da370 0xff0fe3cffe3f8fc3 0xbfc3f8f3ff8fe3f0

def z27 : W := mkw 0x2eaaa3ea40000000 0x0baaa8fa90000000 0x6fffe3fff0000003 0xdbfff8fffc000000

def z28 : W := mkw 0xafbaa3eadfb68fe8 0x6beea8fab7eda3fa 0xffffe3ffffff8fff 0xfffff8ffffffe3ff

def z29 : W := mkw 0x10100000952c5b30 0x04040000254b16cc 0x900000000d3c7f30 0x24000000034f1fcc

def z30 : W := mkw 0x222027ff60000001 0x088809ffd8000000 0x200003fff0000000 0x080000fffc000000

def z31 : W := mkw 0x6fffffff6fdb6001 0x9bffffffdbf6d800 0xfffffffffffff003 0xfffffffffffffc00

def z32 : W := mkw 0x232003a80a0006a8 0x48c800ea028001aa 0xbf0003fc0e000fff 0xafc000ff038003ff

def z33 : W := mkw 0x0030012005000220 0x000c004801400088 0x10f003000c000701 0x043c00c0030001c0

def z34 : W := mkw 0x6eebb7ff60000001 0x1bbaedffd8000000 0x2ff303fff0000001 0x0bfcc0fffc000000

def z35 : W := mkw 0x0000000090240900 0x0000000024090240 0xf0030303fc3c0f03 0x3c00c0c0ff0f03c0

def z36 : W := mkw 0x6ffb93a80f9a46a8 0xdbfee4ea03e691aa 0x1ff303000c1c0701 0x07fcc0c0030701c0

def z37 : W := mkw 0x222003a8000006a8 0x488800ea000001aa 0x200003fc00000ffc 0x080000ff000003ff

def z38 : W := mkw 0x4ccffc5760000001 0x1333ff15d8000000 0x4ffffc03f0000003 0xd3ffff00fc000000

def z39 : W := mkw 0x2aa803a800000000 0x0aaa00ea00000000 0xaffc03fc03c008ff 0xebff00ff00f0023f

def z40 : W := mkw 0x070282800a120480 0x01c0a0a002848120 0xff03e3c00e3f8fc3 0xbfc0f8f0038fe3f0

def z41 : W := mkw 0x40455c1520000001 0x1011570548000000 0x00001c0000000000 0x0000070000000000

def z42 : W := mkw 0x8402800050160100 0x2100a00014058040 0x00030000701c0000 0x0000c0001c070000

def z43 : W := mkw 0x8706eac64a53a4c4 0x21c1bab19294e931 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z44 : W := mkw 0x0061153120000000 0x0018454c48000000 0x60f31f33f0000003 0x583cc7ccfc000000

def z45 : W := mkw 0x28a8012800000000 0x0a2a004a00000000 0x00fc003c00000000 0x403f000f00000000

def z46 : W := mkw 0x4447fc5760000001 0x1111ff15d8000000 0x4003fc03f0000000 0x1000ff00fc000000

def z47 : W := mkw 0x4ccfd80000000000 0x1333f60000000000 0x4ffffc0000000003 0xd3ffff0000000000

def z48 : W := mkw 0x870282804a120480 0x21c0a0a012848120 0x0f00000000000000 0x03c0000000000000

def z49 : W := mkw 0x011000000f8006a8 0x4044000003e001aa 0x900000000fc00ffc 0x2400000003f003ff

def z50 : W := mkw 0x810000009a368dc0 0x20400000268da370 0x900000000e3f8fc0 0x24000000038fe3f0

def z51 : W := mkw 0x0030012005000220 0x000c004801400088 0xb0f003300d000f33 0x6c3c00cc034003cc

def z52 : W := mkw 0x00046c579065b954 0x00011b15e4196e55 0xf00fffffffffffff 0xfc03ffffffffffff

def z53 : W := mkw 0xc747fac2da7fedc0 0xb1d1feb0b69ffb70 0xff03ffc3fe3fffc3 0xbfc0fff0ff8ffff0

def z54 : W := mkw 0x0010000005c96000 0x8004000001725800 0x0000000001c07000 0x0000000000701c00

def z55 : W := mkw 0xefeffffffa368dc1 0x3bfbfffffe8da370 0xfffffffffe3f8fc3 0xffffffffff8fe3f0

def z56 : W := mkw 0x68e9112820000001 0x1a3a444a08000000 0x00f0000000000000 0x003c000000000000

def z57 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x1ffc03cc0ec007cd 0x87ff00f303b001f3

def z58 : W := mkw 0x8000000090248dc0 0x2000000024092370 0x0000000000000fc0 0x00000000000003f0

def z59 : W := mkw 0x0020012000000220 0x0008004800000088 0x2000033000000f30 0x080000cc000003cc

def z60 : W := mkw 0x000468460041a044 0x00011a1180106811 0xa00ce0fc03c388fe 0xe803383f00f0e23f

def z61 : W := mkw 0x7efffffff52c5b31 0x1fbffffffd4b16cc 0xfffffffffd3c7f33 0xffffffffff4f1fcc

def z62 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff0fe3ffffff8fff 0xffc3f8ffffffe3ff

def z63 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x3ffc03fc0c000703 0xcfff00ff030001c0

def z64 : W := mkw 0x030002800a000480 0x00c000a002800120 0x0f0000c0020000c0 0x83c0003000800030

def z65 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0xc000fc0383e3f8fc 0x30003f00e0f8fe3f

def z66 : W := mkw 0x4ccfd800005b6000 0x9333f6000016d800 0x4ffffc00003ff003 0xd3ffff00000ffc00

def z67 : W := mkw 0x91711531bf3edff0 0x245c454c6fcfb7fc 0xf0f31f33ff3ffff3 0x7c3cc7ccffcffffc

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000c0020008c2 0xa800003000800230

def z69 : W := mkw 0x6effffff65000221 0x1bbfffffd9400088 0xfffffffffd000f33 0xffffffffff4003cc

def z70 : W := mkw 0x9722a7f3fa369ff0 0x25c8a9fcfe8da7fc 0xff03e3f3fe3f8ff3 0xbfc0f8fcff8fe3fc

def z71 : W := mkw 0x44439000001a4000 0x9110e40000069000 0x00030000001c0000 0x0000c00000070000

def z72 : W := mkw 0x870282805a160580 0x21c0a0a016858160 0xbf0303c07e1c0fc3 0xafc0c0f01f8703f0

def z73 : W := mkw 0x4d8ee8460ad3a044 0x9363ba1182b4e811 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z74 : W := mkw 0x015110000fdb6000 0x8054440003f6d800 0xd0f31c000ffff003 0x743cc70003fffc00

def z75 : W := mkw 0xefffffffffffedc1 0xbbfffffffffffb70 0xffffffffffffffc3 0xfffffffffffffff0

def z76 : W := mkw 0x050280000a120000 0x0140a00002848000 0x1f0300000c1c0001 0x07c0c00003070000

def z77 : W := mkw 0x6eefffffe0201811 0x1bbbfffff8080604 0xeffffffff1207833 0xfbfffffffc481e0c

def z78 : W := mkw 0x0000000080201810 0x0000000020080604 0x8000000001207830 0x2000000000481e0c

def z79 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x1ff003000c000701 0x07fc00c0030001c0

def z80 : W := mkw 0x0000204280208840 0x00000810a0082210 0xe000e0c3822388c2 0xb8003830e088e230

def z81 : W := mkw 0x870282805a160580 0x21c0a0a016858160 0x1f0303007c1c0701 0x07c0c0c01f0701c0

def z82 : W := mkw 0x2aa803a800000000 0x0aaa00ea00000000 0x2ffc03fc00000003 0xcbff00ff00000000

def z83 : W := mkw 0x6fffffff6f8006a9 0x5bffffffdbe001aa 0xffffffffffc00fff 0xfffffffffff003ff

def z84 : W := mkw 0x6dffd9280fdb6228 0xdb7ff64a03f6d88a 0xdffffc3c0ffff03f 0xf7ffff0f03fffc0f

def z85 : W := mkw 0x0000041100001010 0x0000010440000404 0x00001c3001007030 0x4000070c00401c0c

def z86 : W := mkw 0x10757d77b56dfb74 0x041d5f5ded5b7edd 0xf0ffffffffffffff 0xfc3fffffffffffff

def z87 : W := mkw 0x000000008061b854 0x0000000020186e15 0x8000000003e3f8fc 0x2000000000f8fe3f

def z88 : W := mkw 0x6eefffffe061b855 0x1bbbfffff8186e15 0xeffffffff3e3f8ff 0xfbfffffffcf8fe3f

def z89 : W := mkw 0x9743b6d3fa3eddd0 0x25d0edb4fe8fb774 0xff03ffc3fe3fffc3 0xbfc0fff0ff8ffff0

def z90 : W := mkw 0x0000245780209854 0x00000915e0082615 0xe000e0ff822388fe 0xb800383fe088e23f

def z91 : W := mkw 0x4ddb90000f9a4000 0x9376e40003e69000 0x1ff300000c1c0001 0x07fcc00003070000

def z92 : W := mkw 0x6fbeebee4f8006a9 0x5befbafb93e001aa 0xbffce3fc0fc00fff 0xefff38ff03f003ff

def z93 : W := mkw 0x2aa827ff60000001 0x0aaa09ffd8000000 0x2ffc03fff0000003 0xcbff00fffc000000

def z94 : W := mkw 0x3bf917b9bfac5fb8 0x4efe45ee6feb17ee 0xfff31f33fd3c7f33 0x7ffcc7ccff4f1fcc

def z95 : W := mkw 0x7effffff65085231 0x1fbfffffd942148c 0x6ffffffff1007033 0xdbfffffffc401c0c

def z96 : W := mkw 0x10200531b0241b30 0x0408014c6c0906cc 0xf0030333fc3c0f33 0x3c00c0ccff0f03cc

def z97 : W := mkw 0x0000000000000000 0x0000000000000000 0x800c000003c00002 0xe003000000f00000

def z98 : W := mkw 0x0051100005084000 0x0014440001421000 0x00f01c0001007000 0x403c070000401c00

def z99 : W := mkw 0x6ffb93a86f9a4001 0x9bfee4ea1be69000 0x1ff303007c1c0001 0x07fcc0c01f070000

def z100 : W := mkw 0x6fffdba86fdb6001 0x9bfff6ea1bf6d800 0xdfffff007ffff003 0xf7ffffc01ffffc00

def z101 : W := mkw 0x4fdfda800fdb6480 0x93f7f6a003f6d920 0xffffffc00fffffc3 0xfffffff003fffff0

def z102 : W := mkw 0x8402a042d0368940 0x2100a810b40da250 0x4003e003f03f8000 0x1000f800fc0fe000

def z103 : W := mkw 0x4dcfd8000a120000 0x1373f60002848000 0xdffffc000e3f8003 0xf7ffff00038fe000

def z104 : W := mkw 0x00044c1500413014 0x0001130540104c05 0x000c1c3c01c0703c 0x4003070f00701c0f

def z105 : W := mkw 0x000468460041a044 0x00011a1180106811 0x000ce0cc02c380cc 0x8003383300b0e033

def z106 : W := mkw 0x6eefffff6041a045 0x1bbbffffd8106811 0x6ffffffff2c380cf 0xdbfffffffcb0e033

def z107 : W := mkw 0x11711531bfac5fb8 0x445c454c6feb17ee 0xf0f31f33fffc7fff 0x7c3cc7ccffff1fff

def z108 : W := mkw 0x4ddfdc150fdb7014 0x9377f70543f6dc05 0xdffffc3c0ffff03f 0xf7ffff0f03fffc0f

def z109 : W := mkw 0x030002800a000480 0x00c000a002800120 0xbf0003c00e000fc3 0xafc000f0038003f0

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00c00fc03c008fe 0xe803003f00f0023f

def z111 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x50f31f03fc3c7701 0x143cc7c0ff0f1dc0

def z112 : W := mkw 0x10757d77b56dfb74 0x041d5f5ded5b7edd 0xf0f3ff33fd3fff33 0x7c3cffccff4fffcc

def z113 : W := mkw 0x6ffb93a80f9a46a8 0xdbfee4ea03e691aa 0xbfff03fc0fdc0fff 0xefffc0ff03f703ff

def z114 : W := mkw 0x10757d77b52c5b30 0x041d5f5ded4b16cc 0xf0fffffffd3c7f33 0xfc3fffffff4f1fcc

def z115 : W := mkw 0x322027fff0241b31 0x0c8809fffc0906cc 0x200003fff0000f30 0x080000fffc0003cc

def z116 : W := mkw 0x10146c57956dfb74 0x04051b15e55b7edd 0xf00cfcff8ffffffe 0xfc033f3fe3ffffff

def z117 : W := mkw 0x8702a6d3da369dd0 0x21c0a9b4f68da774 0xff03fff3ff3ffff3 0xffc0fffcffcffffc

def z118 : W := mkw 0x4ddff8428ffbe840 0x9377fe10a3fefa10 0xfffffcc38ffff8c3 0xffffff30e3fffe30

def z119 : W := mkw 0x10711120350c4320 0x041c44480d4310c8 0x10f303007c1c0701 0x043cc0c01f0701c0

def z120 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x5f03e303fc3f8701 0x17c0f8c0ff0fe1c0

def z121 : W := mkw 0x6fffdba80fdb66a8 0xdbfff6ea03f6d9aa 0xfffffffc0fffffff 0xffffffff03ffffff

def z122 : W := mkw 0x48dd580005c96000 0x9237560001725800 0xc0fcfc0003e3f002 0xf03f3f0000f8fc00

def z123 : W := mkw 0x4d9ec8000fdb6000 0x9367b20003f6d800 0x9f0ce0000ffff000 0xa7c3380003fffc00

def z124 : W := mkw 0x911000009f3edff0 0x2444000027cfb7fc 0x900000000f3ffff0 0x2400000003cffffc

def z125 : W := mkw 0x00044c1500413014 0x0001130540104c05 0xc00cfc3c03e3f03e 0xf0033f0f00f8fc0f

def z126 : W := mkw 0x10755d31b56d7b30 0x041d574c6d5b5ecc 0xf0ffff33ffffff33 0xfc3fffccffffffcc

def z127 : W := mkw 0x3bf917b9bfac5fb8 0x4efe45ee6feb17ee 0xffff1ffffffc7fff 0xffffc7ffffff1fff

def z128 : W := mkw 0x488c480000c12000 0x9223120000304800 0x000c000000c00000 0x0003000000300000

def z129 : W := mkw 0x810000001a160580 0x2040000006858160 0x100000000c1c0700 0x04000000030701c0

def z130 : W := mkw 0x111000009fff7b30 0x8444000027ffdecc 0x900000000fffff30 0x2400000003ffffcc

def z131 : W := mkw 0x5dffdd31bfff7b30 0x977ff74c6fffdecc 0xffffff33ffffff33 0xffffffccffffffcc

def z132 : W := mkw 0x6eefffff60413015 0x1bbbffffd8104c05 0x6ffffffff1c0703f 0xdbfffffffc701c0f

def z133 : W := mkw 0x7fffffffffff7b31 0x9fffffffffffdecc 0xffffffffffffff33 0xffffffffffffffcc

def z134 : W := mkw 0x6fffffff6fdb66a9 0xdbffffffdbf6d9aa 0xffffffffffffffff 0xffffffffffffffff

def z135 : W := mkw 0xabb803a89fb68fe8 0x6aee00ea27eda3fa 0xbffc03fc0fff8fff 0xefff00ff03ffe3ff

def z136 : W := mkw 0x7fffdfb9bfff7fb8 0xdffff7ee6fffdfee 0xffffffffffffffff 0xffffffffffffffff

def z137 : W := mkw 0x5dfb91203f9e4320 0x977ee4480fe790c8 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z138 : W := mkw 0x4447d800005b6000 0x9111f6000016d800 0x4003fc00003ff000 0x1000ff00000ffc00

def z139 : W := mkw 0x00511000952c4900 0x00144400254b1240 0xf0f31f03fd3c7f03 0x7c3cc7c0ff4f1fc0

def z140 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x90f01c300d3c7f30 0x643c070c034f1fcc

def z141 : W := mkw 0x8f9aa2c2dfb68dc0 0x23e6a8b0b7eda370 0xffffe3c3ffff8fc3 0xfffff8f0ffffe3f0

def z142 : W := mkw 0x6bfd5ba80fc966a8 0xdaff56ea03f259aa 0xbffc1ffc0fc07fff 0xefff07ff03f01fff

def z143 : W := mkw 0x0004480000412000 0x0001120000104800 0x000ce00002c38000 0x8003380000b0e000

def z144 : W := mkw 0x09d910000f884000 0x0276440003e21000 0xdfff1c000ffc7003 0xf7ffc70003ff1c00

def z145 : W := mkw 0x2b9802880f8006a8 0x4ae600a203e001aa 0x9f0c00cc0fc00ffc 0xa7c3003303f003ff

def z146 : W := mkw 0x811000009fb68fe8 0x6044000027eda3fa 0x900000000fff8ffc 0x2400000003ffe3ff

def z147 : W := mkw 0x68ed5d3d20000001 0x1a3b574f48000000 0x00fc1c3c00000000 0x403f070f00000000

def z148 : W := mkw 0x0004480400412004 0x0001120100104801 0x000c000c00c0000c 0x0003000300300003

def z149 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xfffffcfc0ffff8ff 0xffffff3f03fffe3f

def z150 : W := mkw 0x3bf913a83f8c47a8 0x4efe44ea0fe311ea 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z151 : W := mkw 0x10457c57b06df954 0x04115f15ec1b7e55 0xe00ffcfff3fff8fe 0xf803ff3ffcfffe3f

def z152 : W := mkw 0x10411000300c4100 0x041044000c031040 0x00030000701c0000 0x0000c0001c070000

def z153 : W := mkw 0x10411411b02c5910 0x041045046c0b1644 0xe0031c33f13c7832 0x7800c70cfc4f1e0c

def z154 : W := mkw 0x226137ff60000001 0x08984dffd8000000 0x60f31ffff0000003 0x583cc7fffc000000

def z155 : W := mkw 0x6eefffff600006a9 0x5bbbffffd80001aa 0x6ffffffff0000fff 0xdbfffffffc0003ff

def z156 : W := mkw 0x6eefffffe061b855 0x1bbbfffff8186e15 0x6ffffffff023f003 0xdbfffffffc08fc00

def z157 : W := mkw 0x0000245760000001 0x00000915d8000000 0x00000003f0000000 0x00000000fc000000

def z158 : W := mkw 0x68fd5d3d25c96001 0x9a3f574f49725800 0x00fc1c3c01c07000 0x403f070f00701c00

def z159 : W := mkw 0x2bb803a80fdb66a8 0xcaee00ea03f6d9aa 0xbffc03fc0fffffff 0xefff00ff03ffffff

def z160 : W := mkw 0xc447f842d07fe940 0xb111fe10b41ffa50 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z161 : W := mkw 0x4ecffac240000000 0x13b3feb090000000 0x6fffffc3f0000003 0xdbfffff0fc000000

def z162 : W := mkw 0xefeffffffa77bdd5 0x3bfbfffffe9def75 0xffffffffffffffff 0xffffffffffffffff

def z163 : W := mkw 0x8706eed7da77bdd4 0x21c1bbb5f69def75 0xff0fffffffffffff 0xffc3ffffffffffff

def z164 : W := mkw 0x8702a2c24a1284c0 0x21c0a8b09284a130 0x0f00e0c0020380c0 0x83c038300080e030

def z165 : W := mkw 0x01146c578fe1befc 0x40451b15e3f86fbf 0xf00cfcff8fe3fffe 0xfc033f3fe3f8ffff

def z166 : W := mkw 0x0898000005800000 0x0226000001600000 0x00fc000001c00000 0x403f000000700000

def z167 : W := mkw 0x6eefffff60412001 0x1bbbffffd8104800 0xeffffffff3e3f003 0xfbfffffffcf8fc00

def z168 : W := mkw 0x0000000080209854 0x0000000020082615 0x00000000000008fc 0x000000000000023f

def z169 : W := mkw 0x0602a2c240000000 0x0180a8b090000000 0x0f00e0c000000000 0x83c0383000000000

def z170 : W := mkw 0x1071153125085230 0x041c454c4942148c 0x00f01c3001007030 0x403c070c00401c0c

def z171 : W := mkw 0x0030012095240b20 0x000c0048254902c8 0xf0f30333fd3c0f33 0x7c3cc0ccff4f03cc

def z172 : W := mkw 0x48dd580005c96000 0x9237560001725800 0x00fc1c0001c07000 0x403f070000701c00

def z173 : W := mkw 0x820022c2d0248dc0 0x208008b0b4092370 0x200003c3f0000fc0 0x080000f0fc0003f0

def z174 : W := mkw 0x0000041180201810 0x0000010460080604 0xe0001c3381207832 0x7800070ce0481e0c

def z175 : W := mkw 0x10755d35b56d7b34 0x041d574d6d5b5ecd 0xf0ff1f3ffdfc7f3f 0x7c3fc7cfff7f1fcf

def z176 : W := mkw 0x8402a04240128040 0x2100a8109004a010 0x0000e00000038000 0x000038000000e000

def z177 : W := mkw 0x0000000090240900 0x0000000024090240 0x20000303f0000f00 0x080000c0fc0003c0

def z178 : W := mkw 0x0071112005084220 0x001c444801421088 0xf0f31f300d3c7f33 0x7c3cc7cc034f1fcc

def z179 : W := mkw 0x10711120b52c5b30 0x041c44482d4b16cc 0x90f303007d3c7f31 0x243cc0c01f4f1fcc

def z180 : W := mkw 0x10200531b0241b30 0x0408014c6c0906cc 0x20000333f0000f30 0x080000ccfc0003cc

def z181 : W := mkw 0x28b8012805800228 0x4a2e004a0160008a 0x00fc003c01c0003c 0x403f000f0070000f

def z182 : W := mkw 0x6fffffffefe1befd 0x5bfffffffbf86fbf 0xffffffffffe3ffff 0xfffffffffff8ffff

def z183 : W := mkw 0x4457d800055b6000 0x9115f6000156d800 0xd0f3fc000d3ff003 0x743cff00034ffc00

def z184 : W := mkw 0x6fefffff6a120001 0x1bfbffffda848000 0xfffffffffe3f8003 0xffffffffff8fe000

def z185 : W := mkw 0x0000000080208840 0x0000000020082210 0x80000000022388c0 0x200000000088e230

def z186 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x4f03e0c3f23f80c0 0x93c0f830fc8fe030

def z187 : W := mkw 0xefefffff6a1284c1 0x3bfbffffda84a130 0x6ffffffff20380c3 0xdbfffffffc80e030

def z188 : W := mkw 0x00000000005b6000 0x800000000016d800 0x00000000003ff000 0x00000000000ffc00

def z189 : W := mkw 0x5477fd77f52c5b31 0x151dff5dfd4b16cc 0xf0f3ff33fd3c7f33 0x7c3cffccff4f1fcc

def z190 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x200c1cff81c078fc 0x4803073fe0701e3f

def z191 : W := mkw 0x031002800f8006a8 0x40c400a003e001aa 0xbf0003c00fc00fff 0xafc000f003f003ff

def z192 : W := mkw 0x2bbc6fff0f8006a8 0x4aef1bffc3e001aa 0xfffcffff8fc00fff 0xffff3fffe3f003ff

def z193 : W := mkw 0x4ccfd80000412000 0x1333f60000104800 0xcffffc0003e3f003 0xf3ffff0000f8fc00

def z194 : W := mkw 0x000448008061b854 0x0001120020186e15 0xc00cfc0003e3f8fe 0xf0033f0000f8fe3f

def z195 : W := mkw 0x7efffffff56dfb75 0x1fbffffffd5b7edd 0xffffffffffffffff 0xffffffffffffffff

def z196 : W := mkw 0xafbeefffdff7bffc 0x6befbbfff7fdefff 0xffffffffffffffff 0xffffffffffffffff

def z197 : W := mkw 0x48d9100005884000 0x9236440001621000 0x00f0000000000000 0x003c000000000000

def z198 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x30f30333fc1c0f31 0x0c3cc0ccff0703cc

def z199 : W := mkw 0xcfdffed7dffffdd4 0xb3f7ffb5f7ffff75 0xffffffffffffffff 0xffffffffffffffff

def z200 : W := mkw 0x9443b453f03ed950 0x2510ed14fc0fb654 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z201 : W := mkw 0x6eeffbee60000001 0x1bbbfefb98000000 0x0fffe3cc70000001 0x83fff8f31c000000

def z202 : W := mkw 0x222003a860000001 0x088800ea18000000 0x0000030070000000 0x000000c01c000000

def z203 : W := mkw 0x6eebb3ea60000001 0x1bbaecfa98000000 0x6ff3e3c3f0000003 0x9bfcf8f0fc000000

def z204 : W := mkw 0x0041100000000000 0x0010440000000000 0x40f31c0000000003 0x503cc70000000000

def z205 : W := mkw 0x0000204290248940 0x00000810a4092250 0xf003e3c3fe3f8fc3 0xbc00f8f0ff8fe3f0

def z206 : W := mkw 0x00046c5700000000 0x00011b15c0000000 0x4000fc0380000000 0x10003f00e0000000

def z207 : W := mkw 0x010000000ad32000 0x8040000002b4c800 0x0000000002c38000 0x0000000000b0e000

def z208 : W := mkw 0x0010000005084000 0x0004000001421000 0x900000000d3c7000 0x24000000034f1c00

def z209 : W := mkw 0x9773b7f3ff3edff0 0x25dcedfcffcfb7fc 0xfff3fff3ff3ffff3 0xfffcfffcffcffffc

def z210 : W := mkw 0x6ceffd7f60000001 0x1b3bff5fd8000000 0x40fffc3ff0000000 0x503fff0ffc000000

def z211 : W := mkw 0x322007b9b0241fb8 0x4c8801ee6c0907ee 0x200003fff0000ffc 0x080000fffc0003ff

def z212 : W := mkw 0x4406e84640000001 0x1101ba1190000000 0x0000e00000000000 0x0000380000000000

def z213 : W := mkw 0x977397b1ff3e5fb0 0x25dce5ec7fcf97ec 0xfff31f33fd3c7f33 0x7ffcc7ccff4f1fcc

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0001c0001207002 0x7000070000481c00

def z215 : W := mkw 0x58fd5d3125c97230 0x963f574c49725c8c 0x00fc1c3001c07030 0x403f070c00701c0c

def z216 : W := mkw 0x6eeb97b960000001 0x1bbae5ee58000000 0x6ff31f33f0000003 0x5bfcc7ccfc000000

def z217 : W := mkw 0x099800000f800000 0x0266000003e00000 0x9ffc00000fc00003 0xe7ff000003f00000

def z218 : W := mkw 0x4447d80000000000 0x1111f60000000000 0x4003fc0000000000 0x1000ff0000000000

def z219 : W := mkw 0x9773b3e2ff3ecfe0 0x25dcecf8bfcfb3f8 0xfff3e3c3fe3f8fc3 0xbffcf8f0ff8fe3f0

def z220 : W := mkw 0x4ddfdc118ffb7810 0x9377f70463fede04 0xfffffc338ffff833 0xffffff0ce3fffe0c

def z221 : W := mkw 0x000468460041a044 0x00011a1180106811 0x0000e00000038000 0x000038000000e000

def z222 : W := mkw 0x68ed7d7f20000001 0x1a3b5f5fc8000000 0x60fcfcff80000002 0xd83f3f3fe0000000

def z223 : W := mkw 0xaf8aa2cadab68dc8 0x6be2a8b2b6ada372 0xff0fe3cffeff8fcf 0xbfc3f8f3ffbfe3f3

def z224 : W := mkw 0x09b801200f800220 0x026e004803e00088 0xbffc03300fc00f33 0xefff00cc03f003cc

def z225 : W := mkw 0x2bb827ff6f8006a9 0x4aee09ffdbe001aa 0xbffc03ffffc00fff 0xefff00fffff003ff

def z226 : W := mkw 0x0000204200008040 0x0000081080002010 0x0000e0c0020380c0 0x800038300080e030

def z227 : W := mkw 0x10711120b52c4b20 0x041c44482d4b12c8 0xf0f30303fc3c0f03 0x3c3cc0c0ff0f03c0

def z228 : W := mkw 0x0030012005000220 0x000c004801400088 0xb0fc03fc0fc00fff 0xec3f00ff03f003ff

def z229 : W := mkw 0x00046c5700000000 0x00011b15c0000000 0x600cfcff80000002 0xd8033f3fe0000000

def z230 : W := mkw 0x4d8ec8000ad32000 0x9363b20002b4c800 0x0f0ce00002c38000 0x83c3380000b0e000

def z231 : W := mkw 0x011000000fdb66a8 0xc044000003f6d9aa 0x900000000ffffffc 0x2400000003ffffff

def z232 : W := mkw 0xabb823eadfa48fe8 0x6aee08fab7e923fa 0xbffc03ffffc00fff 0xefff00fffff003ff

def z233 : W := mkw 0x2b8802880a800488 0x4ae200a202a00122 0x0f00000000000000 0x03c0000000000000

def z234 : W := mkw 0x4ddb90000f9a4000 0x9376e40003e69000 0x9fff00000fdc0003 0xe7ffc00003f70000

def z235 : W := mkw 0xa22027fff0248dc1 0x288809fffc092370 0x200003fff0000fc0 0x080000fffc0003f0

def z236 : W := mkw 0x000020428061b854 0x00000810a0186e15 0xe000e0c383e3f8fe 0xb8003830e0f8fe3f

def z237 : W := mkw 0x78fd5d3db52c5b31 0x1e3f574f6d4b16cc 0xf0ff1f3ffd3c7f33 0x7c3fc7cfff4f1fcc

def z238 : W := mkw 0xefefffff7a160581 0x3bfbffffde858160 0x7ffffffffc1c0703 0xdfffffffff0701c0

def z239 : W := mkw 0x2020012800000228 0x4808004a0000008a 0x0000003c0000003c 0x0000000f0000000f

def z240 : W := mkw 0x68fd5d3d25800229 0x5a3f574f4960008a 0x00fc1c3c01c0003c 0x403f070f0070000f

def z241 : W := mkw 0x4cdfd80005db6000 0x9337f6000176d800 0x40fffc0001fff000 0x503fff00007ffc00

def z242 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x4000fc038023f000 0x10003f00e008fc00

def z243 : W := mkw 0x8732a3e2df368fe0 0x21cca8f8b7cda3f8 0xfff3e3f3ff3f8ff3 0xfffcf8fcffcfe3fc

def z244 : W := mkw 0x0004480000412000 0x0001120000104800 0xe00cfcfc03e3f8fe 0xf8033f3f00f8fe3f

def z245 : W := mkw 0x4ccffc5700000000 0x1333ff15c0000000 0x6ffffcff80000003 0xdbffff3fe0000000

def z246 : W := mkw 0x0020012000000000 0x0008004800000000 0x20f0033000000003 0x483c00cc00000000

def z247 : W := mkw 0x222003a800000000 0x088800ea00000000 0x200003fc00000000 0x080000ff00000000

def z248 : W := mkw 0x4647fed760000001 0x1191ffb5d8000000 0x6f03ffc3f0000003 0x9bc0fff0fc000000

def z249 : W := mkw 0x0000000090240900 0x0000000024090240 0x40030003f03c0000 0x1000c000fc0f0000

def z250 : W := mkw 0x033003a00f0006a0 0x00cc00e803c001a8 0xbff003f00f000ff3 0xeffc00fc03c003fc

def z251 : W := mkw 0x4d8ec8000ad32000 0x9363b20002b4c800 0xdf0fe0000eff8003 0xb7c3f80003bfe000

def z252 : W := mkw 0x0000000000413014 0x0000000000104c05 0x0000000001c0703c 0x0000000000701c0f

def z253 : W := mkw 0x050280009a360900 0x0140a000268d8240 0xff03e303fe3f8f03 0xbfc0f8c0ff8fe3c0

def z254 : W := mkw 0x8602a2c2d0368940 0x2180a8b0b40da250 0x6f03e3c3f03f8003 0x9bc0f8f0fc0fe000

def z255 : W := mkw 0x2aac6fff00000000 0x0aab1bffc0000000 0x6ffcffff80000003 0xdbff3fffe0000000

def z256 : W := mkw 0x4443900060000001 0x1110e40018000000 0x0003000070000000 0x0000c0001c000000

def z257 : W := mkw 0x098800000a800000 0x0262000002a00000 0x0f0c000002c00000 0x83c3000000b00000

def z258 : W := mkw 0x6eaeefff60000001 0x1babbbffd8000000 0x2f0ce3fff0000000 0x8bc338fffc000000

def z259 : W := mkw 0x8753b2c2df3ecdc0 0x21d4ecb0b7cfb370 0xfff3ffc3ff3fffc3 0xfffcfff0ffcffff0

def z260 : W := mkw 0x8702a2c24a1284c0 0x21c0a8b09284a130 0xdf03e0c00e3f80c3 0xb7c0f830038fe030

def z261 : W := mkw 0x099c6c578fe1b854 0x02671b15e3f86e15 0xfffcfcff8fe3f8ff 0xffff3f3fe3f8fe3f

def z262 : W := mkw 0x099800000f800000 0x0266000003e00000 0x1ff000000c000001 0x07fc000003000000

def z263 : W := mkw 0x0004480000412000 0x0001120000104800 0xc00cfc0003e3f002 0xf0033f0000f8fc00

def z264 : W := mkw 0x5dfb9531bfbe5b30 0x977ee54c6fef96cc 0xfff31f33fd3c7f33 0x7ffcc7ccff4f1fcc

def z265 : W := mkw 0x4447fc5760000001 0x1111ff15d8000000 0x600ffcfff0000002 0xd803ff3ffc000000

def z266 : W := mkw 0x0000000000412000 0x0000000000104800 0x8000000003e3f000 0x2000000000f8fc00

def z267 : W := mkw 0x111000009fac5fb8 0x4444000027eb17ee 0x900000000ffc7ffc 0x2400000003ff1fff

def z268 : W := mkw 0x4467fd7760000001 0x1119ff5dd8000000 0x60f3ff33f0000003 0x583cffccfc000000

def z269 : W := mkw 0x68ed7d7fa061b855 0x1a3b5f5fe8186e15 0xe0fcfcff83e3f8fe 0xf83f3f3fe0f8fe3f

def z270 : W := mkw 0x8706eac6da77adc4 0x21c1bab1b69deb71 0xff0fe3cffeff8fcf 0xbfc3f8f3ffbfe3f3

def z271 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0xeffffffff3c008ff 0xfbfffffffcf0023f

def z272 : W := mkw 0x0000041190241910 0x0000010464090644 0xf0031f33fd3c7f33 0x7c00c7ccff4f1fcc

def z273 : W := mkw 0x0606eed740000000 0x0181bbb5d0000000 0x6f0ffffff0000003 0xdbc3fffffc000000

def z274 : W := mkw 0x222027ff80209efc 0x488809ffe00827bf 0x200003ff80000ffc 0x080000ffe00003ff

def z275 : W := mkw 0x4cefdd3120000000 0x133bf74c48000000 0x6fffff33f0000003 0xdbffffccfc000000

def z276 : W := mkw 0x4dffdd312fdb6000 0x937ff74c4bf6d800 0xffffff33fffff003 0xffffffccfffffc00

def z277 : W := mkw 0x2aac6fff8061b854 0x0aab1bffe0186e15 0xeffcffff83e3f8ff 0xfbff3fffe0f8fe3f

def z278 : W := mkw 0x6fffffffeffbf855 0x9bfffffffbfefe15 0xfffffffffffff8ff 0xfffffffffffffe3f

def z279 : W := mkw 0x01146c578ffbf854 0x80451b15e3fefe15 0xf00cfcff8ffff8fe 0xfc033f3fe3fffe3f

def z280 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x9ff003000fc00ffd 0x27fc00c003f003ff

def z281 : W := mkw 0x0000000090240900 0x0000000024090240 0x900000000c3c0f00 0x24000000030f03c0

def z282 : W := mkw 0x6f8eeace4a800489 0x5be3bab392a00122 0x0f0ce0cc02c000cc 0x83c3383300b00033

def z283 : W := mkw 0x10202577b0249b74 0x0408095dec0926dd 0x200003fff0000ffc 0x080000fffc0003ff

def z284 : W := mkw 0x050280000a120000 0x0140a00002848000 0x0f00e00002038000 0x83c038000080e000

def z285 : W := mkw 0x29b801280f800228 0x4a6e004a03e0008a 0x9ffc003c0fc0003f 0xe7ff000f03f0000f

def z286 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x1fffe0000edf8001 0x87fff80003b7e000

def z287 : W := mkw 0x0402800000120000 0x0100a00000048000 0x4003e000003f8000 0x1000f800000fe000

def z288 : W := mkw 0x2bbc4ba80fc126a8 0x4aef12ea03f049aa 0xfffcfffc0fe3ffff 0xffff3fff03f8ffff

def z289 : W := mkw 0x7efb97b9f52c5b31 0x1fbee5ee7d4b16cc 0xfff31f33fd3c7f33 0x7ffcc7ccff4f1fcc

def z290 : W := mkw 0x28b8012805800228 0x4a2e004a0160008a 0xb0fc033c0dc00f3f 0x6c3f00cf037003cf

def z291 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0xe000fcc38223f8c2 0xb8003f30e088fe30

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000fc000008fc 0x0800003f0000023f

def z293 : W := mkw 0x28b8012805800228 0x4a2e004a0160008a 0x00f0000000000000 0x003c000000000000

def z294 : W := mkw 0x48dd580005c96000 0x9237560001725800 0xd0ff1c000dfc7003 0x743fc700037f1c00

def z295 : W := mkw 0x0004480000000000 0x0001120000000000 0x400cfc0000000002 0xd0033f0000000000

def z296 : W := mkw 0xcddff842dfffe940 0xb377fe10b7fffa50 0xdffffc03fffff003 0xf7ffff00fffffc00

def z297 : W := mkw 0x4ddb90000f9a4000 0x9376e40003e69000 0xdff3e0000e3f8003 0xb7fcf800038fe000

def z298 : W := mkw 0x0000204280208840 0x00000810a0082210 0xe00ce0ff83e388fe 0xf803383fe0f8e23f

def z299 : W := mkw 0x0000000080200800 0x0000000020080200 0xe000000380200802 0x38000000e0080200

def z300 : W := mkw 0x4d8a80000a920000 0x9362a00002a48000 0x0f00000000000000 0x03c0000000000000

def z301 : W := mkw 0x0020053120000000 0x0008014c48000000 0x20000333f0000000 0x080000ccfc000000

def z302 : W := mkw 0xefffffffffb68fe9 0x7bffffffffeda3fa 0xffffffffffff8fff 0xffffffffffffe3ff

def z303 : W := mkw 0x1071153125085230 0x041c454c4942148c 0xd0f31c300d3c7033 0x743cc70c034f1c0c

def z304 : W := mkw 0x220022ce40000001 0x088008b390000000 0x000000cc00000000 0x0000003300000000

def z305 : W := mkw 0x4ddfd8000fdb66a8 0xd377f60003f6d9aa 0xdffffc000fffffff 0xf7ffff0003ffffff

def z306 : W := mkw 0x6dffdd3d2fdb6001 0x9b7ff74f4bf6d800 0xdffffc3c0ffff003 0xf7ffff0f03fffc00

def z307 : W := mkw 0x0000041100000000 0x0000010440000000 0x60001c3380000002 0x5800070ce0000000

def z308 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x4ff3ff03f0000001 0x13fcffc0fc000000

def z309 : W := mkw 0x6fffdba80f8006a8 0x5bfff6ea03e001aa 0xfffffffc0fc00fff 0xffffffff03f003ff

def z310 : W := mkw 0x2bb807b98fa01eb8 0x4aee01ee63e807ae 0xfffc1fff8fe07fff 0xffff07ffe3f81fff

def z311 : W := mkw 0x8200028050040580 0x208000a014010160 0x0000030070000700 0x000000c01c0001c0

def z312 : W := mkw 0x4ddffc570fdb6000 0x9377ff15c3f6d800 0xfffffcff8ffff003 0xffffff3fe3fffc00

def z313 : W := mkw 0x688c480c00000001 0x1a23120300000000 0x000c000c00000000 0x0003000300000000

def z314 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c003c01c0003c 0x4003000f0070000f

def z315 : W := mkw 0x0000041500001014 0x0000010540000405 0x0000003c0000003c 0x0000000f0000000f

def z316 : W := mkw 0x6eefffffe0208841 0x1bbbfffff8082210 0xeffffffff22388c3 0xfbfffffffc88e230

def z317 : W := mkw 0x2bbc6fff8fe1befc 0x4aef1bffe3f86fbf 0xfffcffff8fe3ffff 0xffff3fffe3f8ffff

def z318 : W := mkw 0xcfdffac24fdbe4c0 0xb3f7feb093f6f930 0xdffffcc00ffff0c3 0xf7ffff3003fffc30

def z319 : W := mkw 0x00000000000006a8 0x40000000000001aa 0x0000000000000ffc 0x00000000000003ff

def z320 : W := mkw 0xa722a3eada368fe8 0x69c8a8fab68da3fa 0xff03e3fffe3f8fff 0xbfc0f8ffff8fe3ff

def z321 : W := mkw 0x00611531b0240900 0x0018454c6c090240 0xf0f31f33fc3c0f03 0x7c3cc7ccff0f03c0

def z322 : W := mkw 0x10100000150c4320 0x04040000054310c8 0x100000000c1c0700 0x04000000030701c0

def z323 : W := mkw 0x10711120350c4320 0x041c44480d4310c8 0xb0f303307d1c0f33 0x6c3cc0cc1f4703cc

def z324 : W := mkw 0x10100411952c5b30 0x04040104654b16cc 0xf0001c338d3c7f32 0x7c00070ce34f1fcc

def z325 : W := mkw 0x222027ffe0209855 0x088809fff8082615 0x200003fff00008fc 0x080000fffc00023f

def z326 : W := mkw 0x5447fc57f02c5911 0x1511ff15fc0b1644 0x4003fc03f03c7000 0x1000ff00fc0f1c00

def z327 : W := mkw 0x010000000a120000 0x0040000002848000 0x900000000e3f8000 0x24000000038fe000

def z328 : W := mkw 0x2ba803a80a800488 0x4aea00ea02a00122 0x2ffc03fc02c000cf 0xcbff00ff00b00033

def z329 : W := mkw 0x0606eed7c061b854 0x0181bbb5f0186e15 0xef0ffffff3e3f8ff 0xfbc3fffffcf8fe3f

def z330 : W := mkw 0x10711531a5285a30 0x041c454c694a168c 0xe0f01c3381207832 0x783c070ce0481e0c

def z331 : W := mkw 0x222027ff600006a9 0x488809ffd80001aa 0x200003fff0000ffc 0x080000fffc0003ff

def z332 : W := mkw 0x5dfffd77bffffb74 0x977fff5deffffedd 0xffffffffffffffff 0xffffffffffffffff

def z333 : W := mkw 0x4ddffc578ffbf854 0x9377ff15e3fefe15 0xdffffc038ffff003 0xf7ffff00e3fffc00

def z334 : W := mkw 0x222003a8000006a8 0x488800ea000001aa 0x0000030000000700 0x000000c0000001c0

def z335 : W := mkw 0x6cefdd3d20000001 0x1b3bf74f48000000 0x4ffffc3c00000003 0xd3ffff0f00000000

def z336 : W := mkw 0x051280000fdb6000 0x8144a00003f6d800 0xdf03e0000ffff003 0xb7c0f80003fffc00

def z337 : W := mkw 0x4cdfd80005c96000 0x9337f60001725800 0x4ffffc0001c07003 0xd3ffff0000701c00

def z338 : W := mkw 0x000000000041a044 0x0000000000106811 0x0000000002c380cc 0x0000000000b0e033

def z339 : W := mkw 0x922027f3f0249ff0 0x248809fcfc0927fc 0x200003f3f0000ff0 0x080000fcfc0003fc

def z340 : W := mkw 0x4ccffc578061b854 0x1333ff15e0186e15 0xeffffcff83e3f8ff 0xfbffff3fe0f8fe3f

def z341 : W := mkw 0x4447fc57807bf854 0x9111ff15e01efe15 0x4003fc03803ff000 0x1000ff00e00ffc00

def z342 : W := mkw 0x19f91531bfac5b30 0x067e454c6feb16cc 0xffff1f33fffc7f33 0xffffc7ccffff1fcc

def z343 : W := mkw 0x0000204200000000 0x0000081080000000 0x6000e0c380000002 0x98003830e0000000

def z344 : W := mkw 0x0000245780209854 0x00000915e0082615 0xa00c00ff83c008fe 0xe803003fe0f0023f

def z345 : W := mkw 0x00046c5780208840 0x00011b15e0082210 0xe00cfcff822388c2 0xf8033f3fe088e230

def z346 : W := mkw 0x2bf913a80f8846a8 0x4afe44ea03e211aa 0xffff1ffc0ffc7fff 0xffffc7ff03ff1fff

def z347 : W := mkw 0x3bb807b9bfa41fb8 0x4eee01ee6fe907ee 0xbffc03ffffc00fff 0xefff00fffff003ff

def z348 : W := mkw 0x03046ed78a61bcd4 0x00c11bb5e2986f35 0xff0cffff8fe3ffff 0xffc33fffe3f8ffff

def z349 : W := mkw 0x10100000952c5b30 0x04040000254b16cc 0xf0030303fd3c7f33 0x3c00c0c0ff4f1fcc

def z350 : W := mkw 0x030002800a000480 0x00c000a002800120 0x1f0003000c000701 0x07c000c0030001c0

def z351 : W := mkw 0x38f91539b5ac5b38 0x4e3e454e6d6b16ce 0xf0ff1f3ffdfc7f3f 0x7c3fc7cfff7f1fcf

def z352 : W := mkw 0x00044c1500413014 0x0001130540104c05 0xa00c1cfc03c078fe 0xe803073f00f01e3f

def z353 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x400cfccf82e3f0cc 0x90033f33e0b8fc33

def z354 : W := mkw 0x8763b7f3fa368dc0 0x21d8edfcfe8da370 0xfff3fff3fe3f8fc3 0xfffcfffcff8fe3f0

def z355 : W := mkw 0x327117b9b52c5fb8 0x4c9c45ee6d4b17ee 0xf0f31ffffd3c7fff 0x7c3cc7ffff4f1fff

def z356 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x600cfcff8023f002 0xd8033f3fe008fc00

def z357 : W := mkw 0x830002809a368dc0 0x20c000a0268da370 0xbf0003c00e3f8fc3 0xafc000f0038fe3f0

def z358 : W := mkw 0xefebb3eafa368dc1 0x3bfaecfabe8da370 0xfff3e3c3fe3f8fc3 0xbffcf8f0ff8fe3f0

def z359 : W := mkw 0x10000000902c5910 0x04000000240b1644 0x00000000003c7000 0x00000000000f1c00

def z360 : W := mkw 0x0663b7f360000000 0x0198edfcd8000000 0x6ff3fff3f0000003 0xdbfcfffcfc000000

def z361 : W := mkw 0x020022c240000000 0x008008b090000000 0x200003c3f0000000 0x080000f0fc000000

def z362 : W := mkw 0x011000000f8006a8 0x4044000003e001aa 0x100000000c000700 0x04000000030001c0

def z363 : W := mkw 0x00557c578569f854 0x00155f15e15a7e15 0xf0fffcff8ffff8ff 0xfc3fff3fe3fffe3f

def z364 : W := mkw 0x5447dc11b07f7910 0x9511f7046c1fde44 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z365 : W := mkw 0x4ddfd8000f800000 0x1377f60003e00000 0xdffffc000fc00003 0xf7ffff0003f00000

def z366 : W := mkw 0x0051141185285810 0x00144504614a1604 0xf0f31c338d3c7833 0x7c3cc70ce34f1e0c

def z367 : W := mkw 0x5ddfd8009fff7b30 0x9777f60027ffdecc 0xdffffc000fffff33 0xf7ffff0003ffffcc

def z368 : W := mkw 0x00046c570041b054 0x00011b15c0106c15 0x000cfcfc03c3f0fc 0xc0033f3f00f0fc3f

def z369 : W := mkw 0x055390000f1a4000 0x0154e40003c69000 0xdff3fc000f3ff003 0xf7fcff0003cffc00

def z370 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x9ffc03000fc00703 0xe7ff00c003f001c0

def z371 : W := mkw 0x6ecffedf60000001 0x1bb3ffb7d8000000 0x4f0ffccff0000000 0x93c3ff33fc000000

def z372 : W := mkw 0x2bb823ea8fa08ee8 0x4aee08faa3e823ba 0xfffce3ff8fe38fff 0xffff38ffe3f8e3ff

def z373 : W := mkw 0x2ae917b920000000 0x0aba45ee48000000 0x6fff1ffff0000003 0xdbffc7fffc000000

def z374 : W := mkw 0x0702a2c24a000480 0x01c0a8b092800120 0xff03e3c3fe000fc3 0xbfc0f8f0ff8003f0

def z375 : W := mkw 0x2fbaa3ea4f8006a8 0x4beea8fa93e001aa 0xffffe3ffffc00fff 0xfffff8fffff003ff

def z376 : W := mkw 0x4045580000496000 0x9011560000125800 0x00001c0000007000 0x0000070000001c00

def z377 : W := mkw 0x10100000956dfb74 0x04040000255b7edd 0x900000000ffffffc 0x2400000003ffffff

def z378 : W := mkw 0x099c48000fc12000 0x0267120003f04800 0xdffcfc000fe3f003 0xf7ff3f0003f8fc00

def z379 : W := mkw 0xafbaa3eadfb68fe8 0x6beea8fab7eda3fa 0xfff3e3c3fe3f8fc3 0xbffcf8f0ff8fe3f0

def z380 : W := mkw 0x78fd5d3d25085231 0x1e3f574f4942148c 0x00fc1c3c01007030 0x403f070f00401c0c

def z381 : W := mkw 0x00657d7720000000 0x00195f5dc8000000 0x60fffffff0000003 0xd83ffffffc000000

def z382 : W := mkw 0xcfdbb2c2dfbecdc0 0xb3f6ecb0b7efb370 0xfff3e3c3fe3f8fc3 0xbffcf8f0ff8fe3f0

def z383 : W := mkw 0x0010000005000000 0x0004000001400000 0x90f000000d000003 0x643c000003400000

def z384 : W := mkw 0x10611531b02c5b30 0x0418454c6c0b16cc 0x60031f33f03c7f30 0x1800c7ccfc0f1fcc

def z385 : W := mkw 0x4447fc57807bf854 0x9111ff15e01efe15 0xe00ffcff83fff8fe 0xf803ff3fe0fffe3f

def z386 : W := mkw 0x850280009a368dc0 0x2140a000268da370 0xdf03e0000e3f8fc3 0xb7c0f800038fe3f0

def z387 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x200ce0ff82c388fc 0x8803383fe0b0e23f

def z388 : W := mkw 0x3bf913a83f8c47a8 0x4efe44ea0fe311ea 0xbfff03fc7fdc0fff 0xefffc0ff1ff703ff

def z389 : W := mkw 0x8706eed7ca73bcd4 0x21c1bbb5f29cef35 0xef0cfcff83e3f8fe 0xfbc33f3fe0f8fe3f

def z390 : W := mkw 0x0071153125084000 0x001c454c49421000 0xf0f31f33fd3c7003 0x7c3cc7ccff4f1c00

def z391 : W := mkw 0x0200028000000000 0x008000a000000000 0x2f0003c000000003 0x8bc000f000000000

def z392 : W := mkw 0x2b8802880a800488 0x4ae200a202a00122 0xaf0c00fc03c008fe 0xebc3003f00f0023f

def z393 : W := mkw 0x0602a2c2c0208840 0x0180a8b0b0082210 0xef03e3c3f22388c3 0xbbc0f8f0fc88e230

def z394 : W := mkw 0x011448000fdb6000 0x8045120003f6d800 0xd00cfc000ffff002 0xf4033f0003fffc00

def z395 : W := mkw 0x0010000005800228 0x400400000160008a 0x0000000001c0003c 0x000000000070000f

def z396 : W := mkw 0x10246d77b065bb74 0x04091b5dec196edd 0xe00cfffff3e3fffe 0xf8033ffffcf8ffff

def z397 : W := mkw 0xeeeffffff0368941 0x3bbbfffffc0da250 0x6ffffffff03f8003 0xdbfffffffc0fe000

def z398 : W := mkw 0x1020012030040320 0x040800480c0100c8 0x0000030070000700 0x000000c01c0001c0

def z399 : W := mkw 0x0000000010040100 0x0000000004010040 0x100303007c1c0701 0x0400c0c01f0701c0

def z400 : W := mkw 0x10200531b0241b30 0x0408014c6c0906cc 0xe0001f33f1207f32 0x780007ccfc481fcc

def z401 : W := mkw 0x1020053120001230 0x0408014c4800048c 0x0000003000000030 0x0000000c0000000c

def z402 : W := mkw 0x6eefdba800000000 0x1bbbf6ea00000000 0x6ffffffc00000003 0xdbffffff00000000

def z403 : W := mkw 0x5dffd9203fdf6320 0x977ff6480ff7d8c8 0xdfffff007ffff703 0xf7ffffc01ffffdc0

def z404 : W := mkw 0x6eeffffff0240901 0x1bbbfffffc090240 0xfffffffffc3c0f03 0xffffffffff0f03c0

def z405 : W := mkw 0x0071153125000220 0x001c454c49400088 0xf0f31f33fd000f33 0x7c3cc7ccff4003cc

def z406 : W := mkw 0x6fffffff6f8006a9 0x5bffffffdbe001aa 0x7ffffffffc000703 0xdfffffffff0001c0

def z407 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x9f00e0c00e3f8fc0 0xa7c03830038fe3f0

def z408 : W := mkw 0xafbaa3ea4f9286e8 0x6beea8fa93e4a1ba 0xbffce3fc0fc38fff 0xefff38ff03f0e3ff

def z409 : W := mkw 0x5477dd31b57f7b30 0x951df74c6d5fdecc 0xf0f3ff33fd3fff33 0x7c3cffccff4fffcc

def z410 : W := mkw 0x0010000005000220 0x0004000001400088 0x900000000d000f30 0x24000000034003cc

def z411 : W := mkw 0x68ed5d3d20000001 0x1a3b574f48000000 0x60ff1f3ff0000003 0x583fc7cffc000000

def z412 : W := mkw 0x927137f3f52cdff0 0x249c4dfcfd4b37fc 0xf0f31ff3fd3c7ff3 0x7c3cc7fcff4f1ffc

def z413 : W := mkw 0x7effffff750c4321 0x1fbfffffdd4310c8 0x7ffffffffc1c0703 0xdfffffffff0701c0

def z414 : W := mkw 0x011000008fe1befc 0x4044000023f86fbf 0x900000000fe3fffc 0x2400000003f8ffff

def z415 : W := mkw 0x030022c28a208cc0 0x00c008b0a2882330 0xff00e3c38e238fc3 0xbfc038f0e388e3f0

def z416 : W := mkw 0x8406ec57d077b954 0x2101bb15f41dee55 0xe00ffcfff3fff8fe 0xf803ff3ffcfffe3f

def z417 : W := mkw 0x0d9a80000f920000 0x0366a00003e48000 0xdfffe0000fff8003 0xf7fff80003ffe000

def z418 : W := mkw 0xcf8eeac24ad3a4c0 0xb3e3bab092b4e930 0x0f0ce0c002c380c0 0x83c3383000b0e030

def z419 : W := mkw 0xcddfd8009fffedc0 0xb377f60027fffb70 0xdffffc000fffffc3 0xf7ffff0003fffff0

def z420 : W := mkw 0x6fffdba80fdb66a8 0xdbfff6ea03f6d9aa 0xdfffff000ffff703 0xf7ffffc003fffdc0

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0x60030303f0000003 0x1800c0c0fc000000

def z422 : W := mkw 0xeeeffffff0248dc1 0x3bbbfffffc092370 0x6ffffffff0000fc3 0xdbfffffffc0003f0

def z423 : W := mkw 0x7eeffffff02c5911 0x1fbbfffffc0b1644 0x6ffffffff03c7003 0xdbfffffffc0f1c00

def z424 : W := mkw 0x4447fc57605b6001 0x9111ff15d816d800 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z425 : W := mkw 0x49dd58000fdb6000 0x9277560003f6d800 0x90fc1c000ffff000 0x643f070003fffc00

def z426 : W := mkw 0x6bfd5fbd2f8006a9 0x5aff57ef4be001aa 0xbffc1ffc0fc00fff 0xefff07ff03f003ff

def z427 : W := mkw 0x6eefffff605b6001 0x9bbbffffd816d800 0x6ffffffff03ff003 0xdbfffffffc0ffc00

def z428 : W := mkw 0x0402800000000000 0x0100a00000000000 0x4f03e00000000003 0x93c0f80000000000

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000003001000832 0x6800000c0040020c

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000003c008fc 0x2000000000f0023f

def z431 : W := mkw 0x5cffdd31b52c5b30 0x173ff74c6d4b16cc 0xffffff33fd3c7f33 0xffffffccff4f1fcc

def z432 : W := mkw 0x4d8ec8000ad32000 0x9363b20002b4c800 0xcf0cfc0003e3f002 0xf3c33f0000f8fc00

def z433 : W := mkw 0x0000204280208840 0x00000810a0082210 0x4000e00380238000 0x10003800e008e000

def z434 : W := mkw 0x0041141120000000 0x0010450448000000 0x40031c03f0000000 0x1000c700fc000000

def z435 : W := mkw 0x29b801280f8006a8 0x4a6e004a03e001aa 0x90fc003c0fc00ffc 0x643f000f03f003ff

def z436 : W := mkw 0x0004480000412000 0x0001120000104800 0x4000fc000023f000 0x10003f000008fc00

def z437 : W := mkw 0x6fefffff6a800489 0x5bfbffffdaa00122 0x6ffffffff2c000cf 0xdbfffffffcb00033

def z438 : W := mkw 0x0000245780209854 0x00000915e0082615 0xe0001cff812078fe 0x7800073fe0481e3f

def z439 : W := mkw 0x00657d77a061b854 0x00195f5de8186e15 0xe0fffffff3e3f8ff 0xf83ffffffcf8fe3f

def z440 : W := mkw 0x00044c158061b854 0x0001130560186e15 0x800c1c3c03e3f8fc 0x6003070f00f8fe3f

def z441 : W := mkw 0x3bfd7fffbfedfffc 0x4eff5fffeffb7fff 0xffffffffffffffff 0xffffffffffffffff

def z442 : W := mkw 0x00611531a0201810 0x0018454c68080604 0xe0f31f33f1207833 0x783cc7ccfc481e0c

def z443 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x1ffc033c0dc0073d 0x47ff00cf037001cf

def z444 : W := mkw 0x7fffffffffac5fb9 0x5fffffffffeb17ee 0xfffffffffffc7fff 0xffffffffffff1fff

def z445 : W := mkw 0x4c8ec80000000000 0x1323b20000000000 0x0f0ce00000000000 0x83c3380000000000

def z446 : W := mkw 0x6e8eeace40000001 0x1ba3bab390000000 0x6f0fe3cff0000003 0x9bc3f8f3fc000000

def z447 : W := mkw 0x811000009fffedc0 0xa044000027fffb70 0x900000000fffffc0 0x2400000003fffff0

def z448 : W := mkw 0x8702a2c25a1685c0 0x21c0a8b09685a170 0x1f03e3c07e1f87c1 0x87c0f8f01f87e1f0

def z449 : W := mkw 0x28b8012805800228 0x4a2e004a0160008a 0xa0fc00fc03c008fe 0xe83f003f00f0023f

def z450 : W := mkw 0x1010000005085230 0x040400000142148c 0x0000000001007030 0x0000000000401c0c

def z451 : W := mkw 0x810000009a77bdd4 0x20400000269def75 0x900000000ffffffc 0x2400000003ffffff

def z452 : W := mkw 0x4ddfd8000f9a4000 0x9377f60003e69000 0x5ffffc000c1c0003 0xd7ffff0003070000

def z453 : W := mkw 0x10711531350c5330 0x041c454c4d4314cc 0x10f31f307d1c7731 0x443cc7cc1f471dcc

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0xb00003000c000f03 0x2c0000c0030003c0

def z455 : W := mkw 0x00046c5780201810 0x00011b15e0080604 0xe00cfcff81207832 0xf8033f3fe0481e0c

def z456 : W := mkw 0x2ab803a805800228 0x4aae00ea0160008a 0x2ffc03fc01c0003f 0xcbff00ff0070000f

def z457 : W := mkw 0x6ffb93a86f8006a9 0x5bfee4ea1be001aa 0xbfff03fc7fc00fff 0xefffc0ff1ff003ff

def z458 : W := mkw 0x28bc6d7f85e1ba7c 0x4a2f1b5fe1786e9f 0xe0fcfcff83e3f8fe 0xf83f3f3fe0f8fe3f

def z459 : W := mkw 0x8712a2c2dfffedc0 0xa1c4a8b0b7fffb70 0xff03e3c3ffffffc3 0xbfc0f8f0fffffff0

def z460 : W := mkw 0x11711531bfff7b30 0x845c454c6fffdecc 0xf0f31f33ffffff33 0x7c3cc7ccffffffcc

def z461 : W := mkw 0x2b8c6ace0ac1a4cc 0x4ae31ab382b06933 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z462 : W := mkw 0x820026d7d0249dd4 0x208009b5f4092775 0x200003fff0000ffc 0x080000fffc0003ff

def z463 : W := mkw 0x0030012005000220 0x000c004801400088 0x00f0003001000030 0x403c000c0040000c

def z464 : W := mkw 0x2bbc6bee0fc1a6ec 0x4aef1afb83f069bb 0xbffce3fc0fc38fff 0xefff38ff03f0e3ff

def z465 : W := mkw 0x38f9153925885238 0x4e3e454e4962148e 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z466 : W := mkw 0xdffffff3fffffff0 0xb7fffffcfffffffc 0xfffffff3fffffff3 0xfffffffcfffffffc

def z467 : W := mkw 0x80002042d0248940 0x20000810b4092250 0x00000003f0000000 0x00000000fc000000

def z468 : W := mkw 0x327137fff52c5b31 0x0c9c4dfffd4b16cc 0xf0f31ffffd3c7f33 0x7c3cc7ffff4f1fcc

def z469 : W := mkw 0x10511000952c5b30 0x04144400254b16cc 0xd0f31c000d3c7f33 0x743cc700034f1fcc

def z470 : W := mkw 0x8402a042d0368940 0x2100a810b40da250 0xe003e0c3f23f88c2 0xb800f830fc8fe230

def z471 : W := mkw 0x011000000f9a4000 0x8044000003e69000 0x100000000c1c0000 0x0400000003070000

def z472 : W := mkw 0x4ddb90000fdb6000 0x9376e40003f6d800 0x9ff300000ffff001 0x27fcc00003fffc00

def z473 : W := mkw 0x8702a2c2ca328cc0 0x21c0a8b0b28ca330 0xef00e0c3822388c2 0xbbc03830e088e230

def z474 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x0ffcfc0003c3f000 0xc3ff3f0000f0fc00

def z475 : W := mkw 0x010000000a000000 0x0040000002800000 0x9f0000000e000003 0xa7c0000003800000

def z476 : W := mkw 0x830022c2da368dc0 0x20c008b0b68da370 0xb00003c3fe3f8fc0 0x2c0000f0ff8fe3f0

def z477 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0xbff003300d000f33 0x6ffc00cc034003cc

def z478 : W := mkw 0x099800000f8006a8 0x4266000003e001aa 0x9ffc00000fc00fff 0xe7ff000003f003ff

def z479 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0ff1ffffffc7fff 0xfc3fc7ffffff1fff

def z480 : W := mkw 0x2bb803a80f800000 0x0aee00ea03e00000 0xbffc03fc0fc00003 0xefff00ff03f00000

def z481 : W := mkw 0x000468428061a840 0x00011a10a0186a10 0xe00cfcc383e3f8c2 0xf8033f30e0f8fe30

def z482 : W := mkw 0x48dd7c5785e9f854 0x92375f15e17a7e15 0xe0fcfcff83e3f8fe 0xf83f3f3fe0f8fe3f

def z483 : W := mkw 0xafba83a85f9607a8 0x6beea0ea17e581ea 0xbfff03fc7fdc0fff 0xefffc0ff1ff703ff

def z484 : W := mkw 0x0055580005496000 0x0015560001525800 0xd0fffc000ffff003 0xf43fff0003fffc00

def z485 : W := mkw 0x4ddfd8008ffbf854 0x9377f60023fefe15 0xdffffc000ffff8ff 0xf7ffff0003fffe3f

def z486 : W := mkw 0x000468468061b854 0x00011a11a0186e15 0x800ce0cc03e3f8fc 0xa003383300f8fe3f

def z487 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x20f01f33f1007f30 0x483c07ccfc401fcc

def z488 : W := mkw 0x0000245780209854 0x00000915e0082615 0x0000000380000000 0x00000000e0000000

def z489 : W := mkw 0x2200028800000488 0x488000a200000122 0x000000cc000000cc 0x0000003300000033

def z490 : W := mkw 0x4547d8000a5b6000 0x9151f6000296d800 0xdf03fc000e3ff003 0xb7c0ff00038ffc00

def z491 : W := mkw 0x830022c2da248dc0 0x20c008b0b6892370 0xbf0003c3fe000fc3 0xafc000f0ff8003f0

def z492 : W := mkw 0x00044c1500413014 0x0001130540104c05 0x00001c0000007000 0x0000070000001c00

def z493 : W := mkw 0x10711120350c4320 0x041c44480d4310c8 0xd0f31f007d3c7703 0x743cc7c01f4f1dc0

def z494 : W := mkw 0x222003a8000006a8 0x488800ea000001aa 0xa00c03fc03c00ffe 0xe80300ff00f003ff

def z495 : W := mkw 0x81046c579a77bdd4 0x20411b15e69def75 0xf00cfcff8ffffffe 0xfc033f3fe3ffffff

def z496 : W := mkw 0x10411411b02c5910 0x041045046c0b1644 0xf0031f03fc3c7f03 0x3c00c7c0ff0f1fc0

def z497 : W := mkw 0x000024578061b854 0x00000915e0186e15 0xa00000ff83e3f8fc 0x2800003fe0f8fe3f

def z498 : W := mkw 0x6effffff65c96001 0x9bbfffffd9725800 0x6ffffffff1c07003 0xdbfffffffc701c00

def z499 : W := mkw 0x8706eed7da77bdd4 0x21c1bbb5f69def75 0xff03ffc3fe3fffc3 0xbfc0fff0ff8ffff0

def z500 : W := mkw 0xeffffbeadfffefe8 0xfbfffefab7fffbfa 0xffffffffffffffff 0xffffffffffffffff

def z501 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0xc00cfc0383e3f002 0xf0033f00e0f8fc00

def z502 : W := mkw 0x8502a042da368dc0 0x2140a810b68da370 0xd003e003fe3f8fc0 0x3400f800ff8fe3f0

def z503 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x3f0303c3fc1c0fc1 0x0fc0c0f0ff0703f0

def z504 : W := mkw 0xcfcffac2da368dc0 0x33f3feb0b68da370 0xffffffc3fe3f8fc3 0xfffffff0ff8fe3f0

def z505 : W := mkw 0x87028280da368dc0 0x21c0a0a0368da370 0x9f0303007e3f8fc1 0x27c0c0c01f8fe3f0

def z506 : W := mkw 0x4447fc57e061b855 0x1111ff15f8186e15 0x4003fc03f023f000 0x1000ff00fc08fc00

def z507 : W := mkw 0x10711531350c4320 0x041c454c4d4310c8 0x70f31f33fc1c0703 0x5c3cc7ccff0701c0

def z508 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x0ffcfcfc00000000 0xc3ff3f3f00000000

def z509 : W := mkw 0x8702a2c24a1284c0 0x21c0a8b09284a130 0x6f03e3c3f20380c3 0x9bc0f8f0fc80e030

def z510 : W := mkw 0x3af917b9b52c5b30 0x0ebe45ee6d4b16cc 0xffff1ffffd3c7f33 0xffffc7ffff4f1fcc

def z511 : W := mkw 0x2a88028800000000 0x0aa200a200000000 0x0f0c00cc00000000 0x83c3003300000000

def z512 : W := mkw 0x10300120952c5b30 0x040c0048254b16cc 0xb0f003300d3c7f33 0x6c3c00cc034f1fcc

def z513 : W := mkw 0x1071112025084220 0x041c444809421088 0x00f0000000000000 0x003c000000000000

def z514 : W := mkw 0x0602828040000000 0x0180a0a010000000 0x0f03030070000001 0x03c0c0c01c000000

def z515 : W := mkw 0x49dd58000fc96000 0x9277560003f25800 0x9ffc1c000fc07003 0xe7ff070003f01c00

def z516 : W := mkw 0x8000000090368940 0x20000000240da250 0x00000000003f8000 0x00000000000fe000

def z517 : W := mkw 0x8406ec57d077b954 0x2101bb15f41dee55 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z518 : W := mkw 0x2b9802880f800488 0x4ae600a203e00122 0x9ffc00cc0fc000cf 0xe7ff003303f00033

def z519 : W := mkw 0x00046c5780209854 0x00011b15e0082615 0x600cfcff800008fe 0xd8033f3fe000023f

def z520 : W := mkw 0x10457c57b06df954 0x04115f15ec1b7e55 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z521 : W := mkw 0x011000008ffbf854 0x8044000023fefe15 0x900000000ffff8fc 0x2400000003fffe3f

def z522 : W := mkw 0x8702a2c2da77bdd4 0x21c0a8b0b69def75 0xff03e3c3ffffffff 0xbfc0f8f0ffffffff

def z523 : W := mkw 0x011000000f8006a8 0x4044000003e001aa 0xb00c00fc0fc00ffe 0xec03003f03f003ff

def z524 : W := mkw 0x030002809a240d80 0x00c000a026890360 0xff0303c3fe3c0fc3 0xbfc0c0f0ff8f03f0

def z525 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00300000c3c0003 0x3400c000030f0000

def z526 : W := mkw 0x7eeffffff0241b31 0x1fbbfffffc0906cc 0x6ffffffff0000f33 0xdbfffffffc0003cc

def z527 : W := mkw 0x10757d77a569fa74 0x041d5f5de95a7e9d 0xe0fcfcff83e3f8fe 0xf83f3f3fe0f8fe3f

def z528 : W := mkw 0x223003a8050006a8 0x488c00ea014001aa 0xb0f003fc0d000fff 0x6c3c00ff034003ff

def z529 : W := mkw 0xafaaa3eada368dc0 0x2beaa8fab68da370 0xffffe3fffe3f8fc3 0xfffff8ffff8fe3f0

def z530 : W := mkw 0x810020429a368dc0 0x20400810a68da370 0xf000e0c38e3f8fc2 0xbc003830e38fe3f0

def z531 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x5ff3fc000c3ff001 0x17fcff00030ffc00

def z532 : W := mkw 0x22246fff60000001 0x08891bffd8000000 0x600cfffff0000002 0xd8033ffffc000000

def z533 : W := mkw 0x10713573b52cdb70 0x041c4d5ced4b36dc 0xf0f3fff3ff3ffff3 0xfc3cfffcffcffffc

def z534 : W := mkw 0x6fbecba80fd326a8 0xdbefb2ea03f4c9aa 0xbffce3fc0fc38fff 0xefff38ff03f0e3ff

def z535 : W := mkw 0x10611531b02c5910 0x0418454c6c0b1644 0x60f31f33f03c7003 0x583cc7ccfc0f1c00

def z536 : W := mkw 0x2fba83a80f9206a8 0x4beea0ea03e481aa 0xffffe3fc0fff8fff 0xfffff8ff03ffe3ff

def z537 : W := mkw 0x4dcfd8000adb6000 0x9373f60002b6d800 0x4f0ffc0002fff000 0x93c3ff0000bffc00

def z538 : W := mkw 0x820022c2d0248dc0 0x208008b0b4092370 0xf00303c3fc3c0fc3 0x3c00c0f0ff0f03f0

def z539 : W := mkw 0x0200028000000480 0x008000a000000120 0x200003c000000fc0 0x080000f0000003f0

def z540 : W := mkw 0x4447fc57e061b855 0x1111ff15f8186e15 0xe00ffcfff3e3f8fe 0xf803ff3ffcf8fe3f

def z541 : W := mkw 0x00044c1500000000 0x0001130540000000 0x000c1c3c00000000 0x4003070f00000000

def z542 : W := mkw 0x0051100005084000 0x0014440001421000 0x10f300000c1c0001 0x043cc00003070000

def z543 : W := mkw 0xffffffffff3edff1 0x3fffffffffcfb7fc 0xffffffffff3ffff3 0xffffffffffcffffc

def z544 : W := mkw 0x22246fffe061b855 0x08891bfff8186e15 0xe00cfffff3e3f8fe 0xf8033ffffcf8fe3f

def z545 : W := mkw 0x00044c1580613814 0x0001130560184e05 0xe00c1c3f81e0783e 0x7803070fe0781e0f

def z546 : W := mkw 0x4ddffc576fdb6001 0x9377ff15dbf6d800 0xdffffc03fffff003 0xf7ffff00fffffc00

def z547 : W := mkw 0x0000041180201810 0x0000010460080604 0xe00c1cff83e078fe 0xf803073fe0f81e3f

def z548 : W := mkw 0x6ffb93a86f8006a9 0x5bfee4ea1be001aa 0x1ff303007c000701 0x07fcc0c01f0001c0

def z549 : W := mkw 0x10611531b0241b30 0x0418454c6c0906cc 0x60f31f33f0000f33 0x583cc7ccfc0003cc

def z550 : W := mkw 0x4ddff8460fdbe044 0x9377fe1183f6f811 0xdffffccc0ffff0cf 0xf7ffff3303fffc33

def z551 : W := mkw 0x1000000090241b30 0x04000000240906cc 0x0000000000000f30 0x00000000000003cc

def z552 : W := mkw 0x4406c80000532000 0x9101b2000014c800 0x0000e00000038000 0x000038000000e000

def z553 : W := mkw 0x8402a042d0368940 0x2100a810b40da250 0xf003e303fc3f8f03 0x3c00f8c0ff0fe3c0

def z554 : W := mkw 0x7efb93a8750c4321 0x1fbee4ea1d4310c8 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z555 : W := mkw 0xaf8aa2ca4a9284c8 0x6be2a8b292a4a132 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z556 : W := mkw 0x9473b573f53edb70 0x251ced5cfd4fb6dc 0xf0f3ff33fd3fff33 0x7c3cffccff4fffcc

def z557 : W := mkw 0x10300531b52c5b30 0x040c014c6d4b16cc 0xb0000333fd3c7f30 0x2c0000ccff4f1fcc

def z558 : W := mkw 0x8706eac2da77adc0 0x21c1bab0b69deb70 0xff0fffc3ffffffc3 0xffc3fff0fffffff0

def z559 : W := mkw 0x6fffffff8ffbfefc 0xdbffffffe3feffbf 0xffffffff8fffffff 0xffffffffe3ffffff

def z560 : W := mkw 0x10713577b52cdb74 0x041c4d5ded4b36dd 0xf0f31ffffd3c7fff 0x7c3cc7ffff4f1fff

def z561 : W := mkw 0x6eaeebee40000001 0x1babbafb90000000 0x2ffce3fc00000003 0xcbff38ff00000000

def z562 : W := mkw 0x2622a7ff60000001 0x0988a9ffd8000000 0x6f03e3fff0000003 0x9bc0f8fffc000000

def z563 : W := mkw 0x48dd5c1505c97014 0x9237570541725c05 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z564 : W := mkw 0x5dffdd312fdb7230 0x977ff74c4bf6dc8c 0xdffffc300ffff033 0xf7ffff0c03fffc0c

def z565 : W := mkw 0x099800000fdb6000 0x8266000003f6d800 0x9ffc00000ffff003 0xe7ff000003fffc00

def z566 : W := mkw 0x4dcfd8000ad32000 0x9373f60002b4c800 0x4ffffc0002c38003 0xd3ffff0000b0e000

def z567 : W := mkw 0x4d8eec578af3b854 0x9363bb15e2bcee15 0xef0cfcff83e3f8fe 0xfbc33f3fe0f8fe3f

def z568 : W := mkw 0x0402a04240000000 0x0100a81090000000 0x4003e003f0000000 0x1000f800fc000000

def z569 : W := mkw 0x137117b1bf2c5fb0 0x04dc45ec6fcb17ec 0xfff31ff3ff3c7ff3 0xfffcc7fcffcf1ffc

def z570 : W := mkw 0x6aed7fff60000001 0x1abb5fffd8000000 0x20fc1ffff0000000 0x483f07fffc000000

def z571 : W := mkw 0x0004684600000000 0x00011a1180000000 0x000ce0cc00000000 0x8003383300000000

def z572 : W := mkw 0x10711531b56dfb74 0x041c454c6d5b7edd 0xf0f31f33ffffffff 0x7c3cc7ccffffffff

def z573 : W := mkw 0x2bbc4fbd0fc136bc 0x4aef13ef43f04daf 0xbffc1ffc0fc07fff 0xefff07ff03f01fff

def z574 : W := mkw 0x000000008061b854 0x0000000020186e15 0xa00c00fc03e3f8fe 0xe803003f00f8fe3f

def z575 : W := mkw 0x1041141120085010 0x0410450448021404 0x00001c0000007000 0x0000070000001c00

def z576 : W := mkw 0x2b8c6edf8ae1bcdc 0x4ae31bb7e2b86f37 0xef0cfcff83e3f8fe 0xfbc33f3fe0f8fe3f

def z577 : W := mkw 0xef8eeace4a1284c1 0x3be3bab39284a130 0x0f0ce0cc020380c0 0x83c338330080e030

def z578 : W := mkw 0x10755d3525497234 0x041d574d49525c8d 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z579 : W := mkw 0x0000245700000000 0x00000915c0000000 0x200000ff80000000 0x0800003fe0000000

def z580 : W := mkw 0x00346d778561ba74 0x000d1b5de1586e9d 0xf0fcffff8fe3ffff 0xfc3f3fffe3f8ffff

def z581 : W := mkw 0x6e8eeedfc061b855 0x1ba3bbb7f0186e15 0xef0cfcff83e3f8fe 0xfbc33f3fe0f8fe3f

def z582 : W := mkw 0x2b8802880a800488 0x4ae200a202a00122 0xbf0c03cc0ec00fcf 0xafc300f303b003f3

def z583 : W := mkw 0x6effffff65800229 0x5bbfffffd960008a 0x6ffffffff1c0003f 0xdbfffffffc70000f

def z584 : W := mkw 0x2aa803a8000006a8 0x4aaa00ea000001aa 0x2ffc03fc00000fff 0xcbff00ff000003ff

def z585 : W := mkw 0x0030053185201a30 0x000c014c6148068c 0xf0f01f338d207f33 0x7c3c07cce3481fcc

def z586 : W := mkw 0x6eeb93a860000001 0x1bbae4ea18000000 0x2fff03fc70000003 0xcbffc0ff1c000000

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000e00002238002 0xb00038000088e000

def z588 : W := mkw 0x8702a2c25a160580 0x21c0a8b096858160 0x7f03e3c3fc1c0703 0x9fc0f8f0ff0701c0

def z589 : W := mkw 0x00046c5700413014 0x00011b15c0104c05 0x600cfcff81c0703e 0xd8033f3fe0701c0f

def z590 : W := mkw 0x870282805a160580 0x21c0a0a016858160 0xdf03e3007e3f8703 0xb7c0f8c01f8fe1c0

def z591 : W := mkw 0x010000000a800488 0x4040000002a00122 0x0000000002c000cc 0x0000000000b00033

def z592 : W := mkw 0x0061153120000000 0x0018454c48000000 0x00f01c3000000000 0x403c070c00000000

def z593 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x0ffc00fc03c000fc 0xc3ff003f00f0003f

def z594 : W := mkw 0xc747fed7fa368dc1 0x31d1ffb5fe8da370 0xff03ffc3fe3f8fc3 0xbfc0fff0ff8fe3f0

def z595 : W := mkw 0x6e8a828840000001 0x1ba2a0a210000000 0x0f00000000000000 0x03c0000000000000

def z596 : W := mkw 0x0602a2c2d0240900 0x0180a8b0b4090240 0xff03e3c3fc3c0f03 0xbfc0f8f0ff0f03c0

def z597 : W := mkw 0x0702a2c24a120000 0x01c0a8b092848000 0xff03e3c3fe3f8003 0xbfc0f8f0ff8fe000

def z598 : W := mkw 0x233003a80f8006a8 0x48cc00ea03e001aa 0xb00003fc0fc00ffc 0x2c0000ff03f003ff

def z599 : W := mkw 0x2ab803a8058006a8 0x4aae00ea016001aa 0x20fc03fc01c00ffc 0x483f00ff007003ff

def z600 : W := mkw 0x00046c5700412000 0x00011b15c0104800 0xe00cfcff83e3f002 0xf8033f3fe0f8fc00

def z601 : W := mkw 0x099800000f800000 0x0266000003e00000 0xbffc00fc0fc008ff 0xefff003f03f0023f

def z602 : W := mkw 0xcfdfda805fdf6580 0xb3f7f6a017f7d960 0xdfffff007ffff703 0xf7ffffc01ffffdc0

def z603 : W := mkw 0x977393a07f1e47a0 0x25dce4e81fc791e8 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z604 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x1fff1c000ddc7001 0x47ffc70003771c00

def z605 : W := mkw 0x010000000a000480 0x0040000002800120 0x900000000e000fc0 0x24000000038003f0

def z606 : W := mkw 0x2ba803a80a000480 0x0aea00ea02800120 0xbffc03fc0e000fc3 0xefff00ff038003f0

def z607 : W := mkw 0x5ddfdc11bfff7910 0x9777f7046fffde44 0xdffffc03fffff003 0xf7ffff00fffffc00

def z608 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0xe000fc338123f832 0x78003f0ce048fe0c

def z609 : W := mkw 0x0000245380209850 0x00000914e0082614 0xe000fcf38323f8f2 0xf8003f3ce0c8fe3c

def z610 : W := mkw 0x4fdffac24fdb6000 0x93f7feb093f6d800 0xffffffc3fffff003 0xfffffff0fffffc00

def z611 : W := mkw 0x810000009a368dc0 0x20400000268da370 0xf0030303fe3f8fc3 0x3c00c0c0ff8fe3f0

def z612 : W := mkw 0x0506ec578a73b854 0x0141bb15e29cee15 0xff0ffcff8ffff8ff 0xffc3ff3fe3fffe3f

def z613 : W := mkw 0x1071153125085230 0x041c454c4942148c 0x60f31f33f1007033 0x583cc7ccfc401c0c

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z615 : W := mkw 0x0061112020000000 0x0018444808000000 0x00f3030070000001 0x003cc0c01c000000

def z616 : W := mkw 0x6fffdba80fdb6000 0x9bfff6ea03f6d800 0xfffffffc0ffff003 0xffffffff03fffc00

def z617 : W := mkw 0x4557d8000fdb6000 0x9155f60003f6d800 0xd003fc000ffff000 0x3400ff0003fffc00

def z618 : W := mkw 0x4ddb90000f9a4000 0x9376e40003e69000 0xdff31c000d3c7003 0x77fcc700034f1c00

def z619 : W := mkw 0x2aa803a800000000 0x0aaa00ea00000000 0x0ff0030000000001 0x03fc00c000000000

def z620 : W := mkw 0x2bb803a89fa40fa8 0x4aee00ea27e903ea 0xffff03fffffc0fff 0xffffc0ffffff03ff

def z621 : W := mkw 0xa22023ead0248fe8 0x688808fab40923fa 0x200003fff0000ffc 0x080000fffc0003ff

def z622 : W := mkw 0xa722a7fffa368dc1 0x29c8a9fffe8da370 0xff03e3fffe3f8fc3 0xbfc0f8ffff8fe3f0

def z623 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0xbff003c00e000fc3 0xaffc00f0038003f0

def z624 : W := mkw 0x3bb803a89fac5fb8 0x4eee00ea27eb17ee 0xbffc03fc0ffc7fff 0xefff00ff03ff1fff

def z625 : W := mkw 0x6eefffffe0209855 0x1bbbfffff8082615 0x6ffffffff00008ff 0xdbfffffffc00023f

def z626 : W := mkw 0x6eefdba860000001 0x1bbbf6ea18000000 0x4fffff0070000003 0xd3ffffc01c000000

def z627 : W := mkw 0x0000204280208840 0x00000810a0082210 0x200000c3800008c0 0x08000030e0000230

def z628 : W := mkw 0x82046ed7d065bdd4 0x20811bb5f4196f75 0xe00cfffff3e3fffe 0xf8033ffffcf8ffff

def z629 : W := mkw 0x6fdfface4fdb6001 0x9bf7feb393f6d800 0xdffffccc0ffff003 0xf7ffff3303fffc00

def z630 : W := mkw 0x2020053d20000001 0x0808014f48000000 0x0000003c00000000 0x0000000f00000000

def z631 : W := mkw 0x87028280da360d80 0x21c0a0a0368d8360 0xff030303fc3c0f03 0x3fc0c0c0ff0f03c0

def z632 : W := mkw 0x6fdfda880fdb6488 0xdbf7f6a203f6d922 0xdffffccc0ffff0cf 0xf7ffff3303fffc33

def z633 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x2f00e3c3f2038fc0 0x8bc038f0fc80e3f0

def z634 : W := mkw 0x8712a2c2dfb68fe8 0x61c4a8b0b7eda3fa 0xff03e3c3ffff8fff 0xbfc0f8f0ffffe3ff

def z635 : W := mkw 0x6fefffff6a000481 0x1bfbffffda800120 0xfffffffffe000fc3 0xffffffffff8003f0

def z636 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x6000fcff8023f8fc 0x18003f3fe008fe3f

def z637 : W := mkw 0x2bb827ff8fa09efc 0x4aee09ffe3e827bf 0xbffc03ff8fc00fff 0xefff00ffe3f003ff

def z638 : W := mkw 0x10511411b52c5910 0x041445046d4b1644 0xd0f31c03fd3c7003 0x743cc700ff4f1c00

def z639 : W := mkw 0x0004480000412000 0x0001120000104800 0x000c1c0001c07000 0x4003070000701c00

def z640 : W := mkw 0x6e8eeace4041a045 0x1ba3bab390106811 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z641 : W := mkw 0x6fefffff6ad32001 0x9bfbffffdab4c800 0x6ffffffff2c38003 0xdbfffffffcb0e000

def z642 : W := mkw 0x000468468061a844 0x00011a11a0186a11 0xe00ce0cf82e388ce 0xb8033833e0b8e233

def z643 : W := mkw 0x0888000000000000 0x0222000000000000 0x0ffc000000000003 0xc3ff000000000000

def z644 : W := mkw 0x58fd5d31b5ed7b30 0x963f574c6d7b5ecc 0xf0ff1f33fdfc7f33 0x7c3fc7ccff7f1fcc

def z645 : W := mkw 0x2ba803a80a8006a8 0x4aea00ea02a001aa 0x2f0c03fc02c00ffc 0x8bc300ff00b003ff

def z646 : W := mkw 0x0b9802800f800480 0x02e600a003e00120 0xbffc03c00fc00fc3 0xefff00f003f003f0

def z647 : W := mkw 0x820022c2400084c0 0x208008b090002130 0x000000c0000000c0 0x0000003000000030

def z648 : W := mkw 0x00046c570041a044 0x00011b15c0106811 0x600cfcff82c380ce 0xd8033f3fe0b0e033

def z649 : W := mkw 0x011000000f800000 0x0044000003e00000 0x900000000fc00000 0x2400000003f00000

def z650 : W := mkw 0x22246fff8061befc 0x48891bffe0186fbf 0xe00cffff83e3fffe 0xf8033fffe0f8ffff

def z651 : W := mkw 0x6fffffff6f9a4001 0x9bffffffdbe69000 0x7ffffffffc1c0003 0xdfffffffff070000

def z652 : W := mkw 0x6eefdfbd60000001 0x1bbbf7ef58000000 0x0fff1f3c70000001 0x43ffc7cf1c000000

def z653 : W := mkw 0x6ecfface40000001 0x1bb3feb390000000 0x4ffffccc00000003 0xd3ffff3300000000

def z654 : W := mkw 0x68fd592805c96228 0xda3f564a0172588a 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z655 : W := mkw 0xc447fc57f0368941 0x3111ff15fc0da250 0x4003fc03f03f8000 0x1000ff00fc0fe000

def z656 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x400cfc3f81e3f03c 0x50033f0fe078fc0f

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c00cc02c000cc 0x8003003300b00033

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c00fc00000002 0xc803003f00000000

def z659 : W := mkw 0x0000041180201810 0x0000010460080604 0x40001c0380207000 0x10000700e0081c00

def z660 : W := mkw 0xcf8eeac2daf7adc0 0xb3e3bab0b6bdeb70 0xff0fe3c3feff8fc3 0xbfc3f8f0ffbfe3f0

def z661 : W := mkw 0x0502a0428a328840 0x0140a810a28ca210 0xff03e0c38e3f88c3 0xbfc0f830e38fe230

def z662 : W := mkw 0x820022c2d0248dc0 0x208008b0b4092370 0xe000e3c3f2238fc2 0xb80038f0fc88e3f0

def z663 : W := mkw 0x6f8eeace4ad32001 0x9be3bab392b4c800 0x0f0ce0cc02c38000 0x83c3383300b0e000

def z664 : W := mkw 0x030002800a000480 0x00c000a002800120 0xbf0c03fc0fc00fff 0xefc300ff03f003ff

def z665 : W := mkw 0x6f8eca880ad32488 0xdbe3b2a202b4c922 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z666 : W := mkw 0x10511411b52c5b30 0x041445046d4b16cc 0xd0031c03fd3c7f30 0x3400c700ff4f1fcc

def z667 : W := mkw 0x4d9ec8000fd32000 0x9367b20003f4c800 0x9ffce0000fc38003 0xe7ff380003f0e000

def z668 : W := mkw 0x6aed5fbd20000001 0x1abb57ef48000000 0x2ffc1ffc00000003 0xcbff07ff00000000

def z669 : W := mkw 0x28bc4d3d05c1323c 0x4a2f134f41704c8f 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z670 : W := mkw 0xbffbb7fbffbedff8 0x6ffeedfeffefb7fe 0xffffffffffffffff 0xffffffffffffffff

def z671 : W := mkw 0x8602a2c2d0368dc0 0x2180a8b0b40da370 0x6003e3c3f03f8fc0 0x1800f8f0fc0fe3f0

def z672 : W := mkw 0x6effffff65084001 0x1bbfffffd9421000 0xfffffffffd3c7003 0xffffffffff4f1c00

def z673 : W := mkw 0x15739531bf3e5b30 0x055ce54c6fcf96cc 0xfff3ff33ff3fff33 0xfffcffccffcfffcc

def z674 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x3ff003fc0c000ffd 0x0ffc00ff030003ff

def z675 : W := mkw 0x9712a2c2df3edff0 0x25c4a8b0b7cfb7fc 0xff03e3c3ff3ffff3 0xbfc0f8f0ffcffffc

def z676 : W := mkw 0x000000008061b854 0x0000000020186e15 0x000000000023f000 0x000000000008fc00

def z677 : W := mkw 0x0000041180201810 0x0000010460080604 0x2000003380000830 0x0800000ce000020c

def z678 : W := mkw 0x4dffd9200fdb6220 0x937ff64803f6d888 0xffffff300fffff33 0xffffffcc03ffffcc

def z679 : W := mkw 0x8702a2c24a1284c0 0x21c0a8b09284a130 0xbf00e3c00e038fc3 0xafc038f00380e3f0

def z680 : W := mkw 0x000004118061b854 0x0000010460186e15 0xe0001c3383e3f8fe 0x7800070ce0f8fe3f

def z681 : W := mkw 0x6fffffff6f800001 0x1bffffffdbe00000 0xffffffffffc00003 0xfffffffffff00000

def z682 : W := mkw 0x8602a2c2d0248dc0 0x2180a8b0b4092370 0x6f03e3c3f0000fc3 0x9bc0f8f0fc0003f0

def z683 : W := mkw 0x8702a6d7da369dd4 0x21c0a9b5f68da775 0xff03e3fffe3f8fff 0xbfc0f8ffff8fe3ff

def z684 : W := mkw 0x48cd580000000000 0x1233560000000000 0x00fc1c0000000000 0x403f070000000000

def z685 : W := mkw 0x0041100000084000 0x0010440000021000 0x40031c00003c7000 0x1000c700000f1c00

def z686 : W := mkw 0x00044c1180613810 0x0001130460184e04 0xe00cfc3383e3f832 0xf8033f0ce0f8fe0c

def z687 : W := mkw 0x6667ffff60000001 0x1999ffffd8000000 0x6003fffff0000000 0x1800fffffc000000

def z688 : W := mkw 0x10300531b5241b30 0x040c014c6d4906cc 0xb0f00333fd000f33 0x6c3c00ccff4003cc

def z689 : W := mkw 0x2ab803a805000220 0x0aae00ea01400088 0xbffc03fc0d000f33 0xefff00ff034003cc

def z690 : W := mkw 0x1071153125085230 0x041c454c4942148c 0xb0f01f300d007f33 0x6c3c07cc03401fcc

def z691 : W := mkw 0x6e8eeedf40000001 0x1ba3bbb7d0000000 0x6f0cfcff80000002 0xdbc33f3fe0000000

def z692 : W := mkw 0x0506c8000a532000 0x0141b2000294c800 0xdf0ffc000ffff003 0xf7c3ff0003fffc00

def z693 : W := mkw 0x9777fff7ff7ffff4 0x25ddfffdffdffffd 0xffffffffffffffff 0xffffffffffffffff

def z694 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x40f31c33f13c7030 0x503cc70cfc4f1c0c

def z695 : W := mkw 0xefeb93a87a160581 0x3bfae4ea1e858160 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z696 : W := mkw 0x8502a042da368940 0x2140a810b68da250 0xdf03e003fe3f8003 0xb7c0f800ff8fe000

def z697 : W := mkw 0x68ed5d3d20413015 0x1a3b574f48104c05 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z698 : W := mkw 0x013001200f8006a8 0x404c004803e001aa 0xb0f003300fc00fff 0x6c3c00cc03f003ff

def z699 : W := mkw 0x0000204600008044 0x0000081180002011 0x000000cc000000cc 0x0000003300000033

def z700 : W := mkw 0x4447d800005b6000 0x9111f6000016d800 0xc00ffc0003fff002 0xf003ff0000fffc00

def z701 : W := mkw 0x2bf917b92f8006a8 0x4afe45ee4be001aa 0xffff1fffffc00fff 0xffffc7fffff003ff

def z702 : W := mkw 0x810000000a1284c0 0x204000000284a130 0x00000000020380c0 0x000000000080e030

def z703 : W := mkw 0x1673b7f3f52c5b30 0x059cedfcfd4b16cc 0xfff3fff3fd3c7f33 0xfffcfffcff4f1fcc

def z704 : W := mkw 0x4ccb900000000000 0x1332e40000000000 0x0ff3000000000001 0x03fcc00000000000

def z705 : W := mkw 0x2bb803a88fe1befc 0x4aee00ea23f86fbf 0xbffc03fc0fe3ffff 0xefff00ff03f8ffff

def z706 : W := mkw 0x2888000800800008 0x4a22000200200002 0x000c000c00c0000c 0x0003000300300003

def z707 : W := mkw 0x2bbc6fff8fe1befc 0x4aef1bffe3f86fbf 0x5ff0ff038c23f701 0x17fc3fc0e308fdc0

def z708 : W := mkw 0x6eefffff6041b055 0x1bbbffffd8106c15 0x6ffffffff3c3f0ff 0xdbfffffffcf0fc3f

def z709 : W := mkw 0xe9ed5d3dba368dc1 0x3a7b574f6e8da370 0x90fc1c3c0e3f8fc0 0x643f070f038fe3f0

def z710 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x7f03e3c3fc3f8703 0x9fc0f8f0ff0fe1c0

def z711 : W := mkw 0x4557fc576f8006a9 0x5155ff15dbe001aa 0xd003fc03ffc00ffc 0x3400ff00fff003ff

def z712 : W := mkw 0x4ccfd800005b6000 0x9333f6000016d800 0xcffffc0003fff003 0xf3ffff0000fffc00

def z713 : W := mkw 0x4ddbb4578fbad854 0x9376ed15e3eeb615 0x3ff300ff8c1c08fd 0x0ffcc03fe307023f

def z714 : W := mkw 0x8702a2c2dab68dc8 0x61c0a8b0b6ada372 0xff03e3c3feff8fcf 0xbfc0f8f0ffbfe3f3

def z715 : W := mkw 0x2bb803a80f8846a8 0x4aee00ea03e211aa 0xbffc03fc0ffc7fff 0xefff00ff03ff1fff

def z716 : W := mkw 0x2aac6fff60000001 0x0aab1bffd8000000 0x6ffcfffff0000003 0xdbff3ffffc000000

def z717 : W := mkw 0x78fd5d3925c97238 0xde3f574e49725c8e 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z718 : W := mkw 0x6eefffff60008041 0x1bbbffffd8002010 0x6ffffffff20380c3 0xdbfffffffc80e030

def z719 : W := mkw 0x00511411952c5910 0x00144504654b1644 0xf0f31f33fd3c7f33 0x7c3cc7ccff4f1fcc

def z720 : W := mkw 0x3bc91699baac5d98 0x4ef245a66eab1766 0x4f0f1ccff2fc70cc 0x93c3c733fcbf1c33

def z721 : W := mkw 0x2aa803a800000000 0x0aaa00ea00000000 0x6fff03fff0000003 0xdbffc0fffc000000

def z722 : W := mkw 0x011000009fa40fa8 0x4044000027e903ea 0x900000000ffc0ffc 0x2400000003ff03ff

def z723 : W := mkw 0xef8eeaca4ad3a4c8 0xfbe3bab292b4e932 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z724 : W := mkw 0xcadd7ac2d5ededc0 0xb2b75eb0b57b7b70 0x20fc1fc3f1c07fc0 0x483f07f0fc701ff0

def z725 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x3ffc03fc0dc00ffd 0x4fff00ff037003ff

def z726 : W := mkw 0x6eefffff60000489 0x5bbbffffd8000122 0x6ffffffff00000cf 0xdbfffffffc000033

def z727 : W := mkw 0x4667fff760000001 0x1199fffdd8000000 0x6ff3fff3f0000003 0xdbfcfffcfc000000

def z728 : W := mkw 0xb22027fff0249ff1 0x2c8809fffc0927fc 0x200003fff0000ff0 0x080000fffc0003fc

def z729 : W := mkw 0x6eefffff6041a045 0x1bbbffffd8106811 0x6ffffffff0038003 0xdbfffffffc00e000

def z730 : W := mkw 0x0030053195241b30 0x000c014c654906cc 0xf0f31f33fd3c7f33 0x7c3cc7ccff4f1fcc

def z731 : W := mkw 0x7e9eeaced52c5b31 0x1fa7bab3b54b16cc 0x9f0ce0cc0d3c7f30 0xa7c33833034f1fcc

def z732 : W := mkw 0x6ddfd80c0fdb6001 0x9b77f60303f6d800 0xdffffc0c0ffff003 0xf7ffff0303fffc00

def z733 : W := mkw 0x0071153125084220 0x001c454c49421088 0xf0f31f33fd3c7f33 0x7c3cc7ccff4f1fcc

def z734 : W := mkw 0xacbaa16ad5b68b68 0x6b2ea85ab56da2da 0x40ffe03ff1ff803c 0x503ff80ffc7fe00f

def z735 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff03e3f3ff3f8ff3 0xffc0f8fcffcfe3fc

def z736 : W := mkw 0x6eeffbee60000001 0x1bbbfefb98000000 0x6fffe3cff0000003 0x9bfff8f3fc000000

def z737 : W := mkw 0x2ba803a80a000480 0x0aea00ea02800120 0xbffc03fc0fc00fff 0xefff00ff03f003ff

def z738 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x800cfcfc03e3f8fc 0xe0033f3f00f8fe3f

def z739 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0xffff03ffffc00fff 0xffffc0fffff003ff

def z740 : W := mkw 0x6667dba8005b66a8 0xd999f6ea0016d9aa 0x6003fffc003ffffc 0x1800ffff000fffff

def z741 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0xfffc1ffc0fe07fff 0xffff07ff03f81fff

def z742 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff03ffc3ff3fffc3 0xffc0fff0ffcffff0

def z743 : W := mkw 0x111000009fedfffc 0x4444000027fb7fff 0x900000000ffffffc 0x2400000003ffffff

def z744 : W := mkw 0x111000009ffffb74 0x8444000027fffedd 0x900000000ffffffc 0x2400000003ffffff

def z745 : W := mkw 0x8702a2c25a160580 0x21c0a8b096858160 0xff03e3c3fe3f8703 0xbfc0f8f0ff8fe1c0

def z746 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x2fff1ffff0000001 0x4bffc7fffc000000

def z747 : W := mkw 0x6eefffff60800009 0x5bbbffffd8200002 0x6ffffffff0c0000f 0xdbfffffffc300003

def z748 : W := mkw 0xa702a2ceda368dc1 0x29c0a8b3b68da370 0xff03e3cffe3f8fc3 0xbfc0f8f3ff8fe3f0

def z749 : W := mkw 0x6eeffbea40000000 0x1bbbfefa90000000 0x6ffffffff0000003 0xdbfffffffc000000

def z750 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x3f03e3c3fe1f8fc1 0x8fc0f8f0ff87e3f0

def z751 : W := mkw 0x10757966354de364 0x041d5e598d5378d9 0x10ffe3cc7edf87cd 0x843ff8f31fb7e1f3

def z752 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x200cfcff83c3f8fc 0xc8033f3fe0f0fe3f

def z753 : W := mkw 0x9773b7f36f1ad6f0 0x25dcedfcdbc6b5bc 0x0ff0fcf00303f0f0 0xc3fc3f3c00c0fc3c

def z754 : W := mkw 0x0000245380209850 0x00000914e0082614 0xe00cfcff83e3f8fe 0xf8033f3fe0f8fe3f

def z755 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff0fe3fffe3f8fc3 0xffc3f8ffff8fe3f0

def z756 : W := mkw 0x2aa827ff60000001 0x0aaa09ffd8000000 0x2ff003fff0000001 0x0bfc00fffc000000

def z757 : W := mkw 0x10711531b52cdb74 0x041c454c6d4b36dd 0xf0f31f33fd3c7fff 0x7c3cc7ccff4f1fff

def z758 : W := mkw 0x111000009fac5b30 0x0444000027eb16cc 0x900000000ffc7f30 0x2400000003ff1fcc

def z759 : W := mkw 0x0702a2c24a120480 0x01c0a8b092848120 0xff03e3c3fe3f8fc3 0xbfc0f8f0ff8fe3f0

def z760 : W := mkw 0x4ddfd8000fdb6480 0x9377f60003f6d920 0xdffffc000fffffc3 0xf7ffff0003fffff0

def z761 : W := mkw 0x4ccffc5760000001 0x1333ff15d8000000 0x6ffffcfff0000003 0xdbffff3ffc000000

def z762 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x4ffffcfff0000000 0xd3ffff3ffc000000

def z763 : W := mkw 0x0622a3e240000000 0x0188a8f890000000 0x6ff3e3f3f0000003 0xdbfcf8fcfc000000

def z764 : W := mkw 0x0d9ec8000fd32000 0x0367b20003f4c800 0xdffffc000ffff003 0xf7ffff0003fffc00

def z765 : W := mkw 0x4dcfd8000a532000 0x1373f6000294c800 0xdffffc000ffff003 0xf7ffff0003fffc00

def z766 : W := mkw 0x00046c579065b954 0x00011b15e4196e55 0xe00ffcfff3fff8fe 0xf803ff3ffcfffe3f

def z767 : W := mkw 0x4eeffff360000000 0x13bbfffcd8000000 0x6ffffff3f0000003 0xdbfffffcfc000000

def z768 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x4fffffcff0000001 0x93fffff3fc000000

def z769 : W := mkw 0x6eefffff605b6001 0x9bbbffffd816d800 0xeffffffff3fff003 0xfbfffffffcfffc00

def z770 : W := mkw 0x2aa803a8000006a8 0x4aaa00ea000001aa 0xaffc03fc03c00fff 0xebff00ff00f003ff

def z771 : W := mkw 0x6eefdfb920000000 0x1bbbf7ee48000000 0x6ffffffff0000003 0xdbfffffffc000000

def z772 : W := mkw 0x5daecd31baf73b30 0x976bb34c6ebdcecc 0x2f0ce333f2c38f30 0x8bc338ccfcb0e3cc

def z773 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0xfffffffffc3c0003 0xffffffffff0f0000

def z774 : W := mkw 0x011000009fff6900 0x8044000027ffda40 0x900000000fffff00 0x2400000003ffffc0

def z775 : W := mkw 0x0557d8000f5b6000 0x0155f60003d6d800 0xdffffc000ffff003 0xf7ffff0003fffc00

def z776 : W := mkw 0x6eeb93a8e061b855 0x1bbae4ea38186e15 0x8ff3030073e3f8fd 0x23fcc0c01cf8fe3f

def z777 : W := mkw 0x8706ce955a573594 0x21c1b3a55695cd65 0x1f0f1f3c7ddc773d 0x47c3c7cf1f771dcf

def z778 : W := mkw 0x111000009fac5fb8 0x4444000027eb17ee 0x900000000d3c7f30 0x24000000034f1fcc

def z779 : W := mkw 0x4ecffed740000000 0x13b3ffb5d0000000 0x6ffffffff0000003 0xdbfffffffc000000

def z780 : W := mkw 0x111000009fbe5b30 0x8444000027ef96cc 0x900000000d3c7f30 0x24000000034f1fcc

def z781 : W := mkw 0x4dcfd8000adb6000 0x9373f60002b6d800 0x4ffffc0002fff003 0xd3ffff0000bffc00

def z782 : W := mkw 0x6aed7fff60000001 0x1abb5fffd8000000 0x2ffc1ffff0000003 0xcbff07fffc000000

def z783 : W := mkw 0x026117b120000000 0x009845ec48000000 0x6ff31ff3f0000003 0xdbfcc7fcfc000000

def z784 : W := mkw 0x6eefffff60496001 0x9bbbffffd8125800 0x6ffffffff0007003 0xdbfffffffc001c00

def z785 : W := mkw 0x6eebb3ea60000001 0x1bbaecfa98000000 0x2ff303c3f0000001 0x0bfcc0f0fc000000

def z786 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xdf03e303fe3f8fc1 0x37c0f8c0ff8fe3f0

def z787 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0ff1f3ffdfc7f3f 0x7c3fc7cfff7f1fcf

def z788 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xdffffc3c0ffff03f 0xf7ffff0f03fffc0f

def z789 : W := mkw 0x2663b7ff60000001 0x0998edffd8000000 0x6ff3fffff0000003 0xdbfcfffffc000000

def z790 : W := mkw 0x4ccfd80000000000 0x1333f60000000000 0x6fffff03f0000003 0xdbffffc0fc000000

def z791 : W := mkw 0x10711531350c4320 0x041c454c4d4310c8 0xf0f31f33fd3c7703 0x7c3cc7ccff4f1dc0

def z792 : W := mkw 0x10711120b52c4b20 0x041c44482d4b12c8 0xf0f31f03fd3c7f03 0x7c3cc7c0ff4f1fc0

def z793 : W := mkw 0x322027fff0249b75 0x0c8809fffc0926dd 0x200003fff0000ffc 0x080000fffc0003ff

def z794 : W := mkw 0x6eebb7fb60000001 0x1bbaedfed8000000 0x6ff3fff3f0000003 0xdbfcfffcfc000000

def z795 : W := mkw 0x6ecffedf60000001 0x1bb3ffb7d8000000 0x4ffffccff0000003 0xd3ffff33fc000000

def z796 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x6ff3ffc3f0000003 0x9bfcfff0fc000000

def z797 : W := mkw 0x811000009fffefe8 0xe044000027fffbfa 0x900000000ffffffc 0x2400000003ffffff

def z798 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0x400cfcff83e3f0fc 0xd0033f3fe0f8fc3f

def z799 : W := mkw 0x6eefffff60532001 0x9bbbffffd814c800 0x6ffffffff0038003 0xdbfffffffc00e000

def z800 : W := mkw 0x6eebb7ff60000001 0x1bbaedffd8000000 0x0ff30303f0000001 0x03fcc0c0fc000000

def z801 : W := mkw 0x8702a2c6da368dc4 0x21c0a8b1b68da371 0xff03e3cffe3f8fcf 0xbfc0f8f3ff8fe3f3

def z802 : W := mkw 0x68fd5d3d25c96229 0xda3f574f4972588a 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z803 : W := mkw 0x6eefffff600006a9 0x5bbbffffd80001aa 0xeffffffff3c00fff 0xfbfffffffcf003ff

def z804 : W := mkw 0x111000009fa41fb8 0x4444000027e907ee 0x900000000fc00ffc 0x2400000003f003ff

def z805 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff03e3c3ffff8fff 0xbfc0f8f0ffffe3ff

def z806 : W := mkw 0x4ddfd8006fdb6001 0x9377f6001bf6d800 0xdffffc007ffff003 0xf7ffff001ffffc00

def z807 : W := mkw 0x80046c57d065b954 0x20011b15f4196e55 0xe00cfcfff3e3f8fe 0xf8033f3ffcf8fe3f

def z808 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0f31f03fc3c7f03 0x3c3cc7c0ff0f1fc0

def z809 : W := mkw 0x6ecfface40000001 0x1bb3feb390000000 0x6fffffcff0000003 0xdbfffff3fc000000

def z810 : W := mkw 0x6ceffd7f60000001 0x1b3bff5fd8000000 0x4ffffc3ff0000003 0xd3ffff0ffc000000

def z811 : W := mkw 0x6eefdfb960000001 0x1bbbf7ee58000000 0x6fffff33f0000003 0xdbffffccfc000000

def z812 : W := mkw 0x2bb803a86f8006a9 0x4aee00ea1be001aa 0xbffc03fc7fc00fff 0xefff00ff1ff003ff

def z813 : W := mkw 0x4ecbb2c240000000 0x13b2ecb090000000 0x6ff3e3c3f0000003 0x9bfcf8f0fc000000

def z814 : W := mkw 0x2ae937ff60000001 0x0aba4dffd8000000 0x6fff1ffff0000003 0xdbffc7fffc000000

def z815 : W := mkw 0x4cdfd80005496000 0x1337f60001525800 0xdffffc000ffff003 0xf7ffff0003fffc00

def z816 : W := mkw 0xa22027ffd0249ffc 0x688809fff40927ff 0x200003fff0000ffc 0x080000fffc0003ff

def z817 : W := mkw 0x8702a2c2da369dd4 0x21c0a8b0b68da775 0xff03e3c3fe3f8fff 0xbfc0f8f0ff8fe3ff

def z818 : W := mkw 0x111000009fff7910 0x8444000027ffde44 0x900000000ffff000 0x2400000003fffc00

def z819 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x9ffc00fc0fc00ffc 0xe7ff003f03f003ff

def z820 : W := mkw 0xeffb93a85f9e47a8 0xfbfee4ea17e791ea 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z821 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff0fe3cffeff8fcf 0xbfc3f8f3ffbfe3f3

def z822 : W := mkw 0x6eeb97b960000001 0x1bbae5ee58000000 0x6fff1ffff0000003 0xdbffc7fffc000000

def z823 : W := mkw 0x87028280da360d80 0x21c0a0a0368d8360 0xff03e303fe3f8f03 0xbfc0f8c0ff8fe3c0

def z824 : W := mkw 0x6eefffff60412001 0x1bbbffffd8104800 0x6ffffffff2c38003 0xdbfffffffcb0e000

def z825 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xdf03e303fe3f8703 0xb7c0f8c0ff8fe1c0

def z826 : W := mkw 0x6f8eeace4ad32489 0xdbe3bab392b4c922 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z827 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0f31f33fffc7fff 0x7c3cc7ccffff1fff

def z828 : W := mkw 0x850280009a368dc0 0x2140a000268da370 0xff03e303fe3f8fc3 0xbfc0f8c0ff8fe3f0

def z829 : W := mkw 0x8502a042da368940 0x2140a810b68da250 0xff03e303fe3f8f03 0xbfc0f8c0ff8fe3c0

def z830 : W := mkw 0x055390000fdb6000 0x8154e40003f6d800 0xdff3fc000ffff003 0xf7fcff0003fffc00

def z831 : W := mkw 0x10711531b5ac5b38 0x441c454c6d6b16ce 0xf0f31f33fdfc7f3f 0x7c3cc7ccff7f1fcf

def z832 : W := mkw 0x911000009f3ecfe0 0x2444000027cfb3f8 0x900000000e3f8fc0 0x24000000038fe3f0

def z833 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0xf00cffff8fe3ffff 0xfc033fffe3f8ffff

def z834 : W := mkw 0x7ffb93a83f9e47a8 0xdffee4ea0fe791ea 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z835 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0xe00ffffff3e3f8ff 0xf803fffffcf8fe3f

def z836 : W := mkw 0x2eaaa7ff60000001 0x0baaa9ffd8000000 0x6fffe3fff0000003 0xdbfff8fffc000000

def z837 : W := mkw 0x6eefffff60413015 0x1bbbffffd8104c05 0xeffffffff3c078ff 0xfbfffffffcf01e3f

def z838 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xfffffc300ffff833 0xffffff0c03fffe0c

def z839 : W := mkw 0x2bb803a80f9a46a8 0xcaee00ea03e691aa 0xbffc03fc0fdc0fff 0xefff00ff03f703ff

def z840 : W := mkw 0x6eaeebee40000001 0x1babbafb90000000 0x6fffe3fff0000003 0xdbfff8fffc000000

def z841 : W := mkw 0x322027ffb0249ffc 0x4c8809ffec0927ff 0x200003fff0000ffc 0x080000fffc0003ff

def z842 : W := mkw 0x0502a0429a368940 0x0140a810a68da250 0xff03e3c3fe3f8fc3 0xbfc0f8f0ff8fe3f0

def z843 : W := mkw 0x9447fc57f07ff954 0x2511ff15fc1ffe55 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z844 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x5ffffc000c3ff003 0xd7ffff00030ffc00

def z845 : W := mkw 0x4ddfd8000fdb66a8 0xd377f60003f6d9aa 0xdffffc000ffff703 0xf7ffff0003fffdc0

def z846 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0xffff03fc0ffc0fff 0xffffc0ff03ff03ff

def z847 : W := mkw 0x6cefdd3d20000001 0x1b3bf74f48000000 0x6fffff3ff0000003 0xdbffffcffc000000

def z848 : W := mkw 0x233027ff6fdb6001 0x88cc09ffdbf6d800 0xb00003fffffff000 0x2c0000fffffffc00

def z849 : W := mkw 0x00044c1180613810 0x0001130460184e04 0xe00cfcff83e3f8fe 0xf8033f3fe0f8fe3f

def z850 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0f3ff33ff3fff33 0xfc3cffccffcfffcc

def z851 : W := mkw 0x5447fc57b07ff954 0x9511ff15ec1ffe55 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z852 : W := mkw 0x4557d8000f5b6000 0x9155f60003d6d800 0xdff3fc000f3ff003 0xf7fcff0003cffc00

def z853 : W := mkw 0x111000009f3e5b30 0x0444000027cf96cc 0x900000000f3fff30 0x2400000003cfffcc

def z854 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xdff3fc000d3ff003 0x77fcff00034ffc00

def z855 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xdff3fc000e3ff003 0xb7fcff00038ffc00

def z856 : W := mkw 0x2eaeefff40000000 0x0babbbffd0000000 0x6ffffffff0000003 0xdbfffffffc000000

def z857 : W := mkw 0x3071153db52c5b31 0x0c1c454f6d4b16cc 0xf0f31f3ffd3c7f33 0x7c3cc7cfff4f1fcc

def z858 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff0fe3c3ffff8fc3 0xffc3f8f0ffffe3f0

def z859 : W := mkw 0x6eefffff60008045 0x1bbbffffd8002011 0x6ffffffff00000cf 0xdbfffffffc000033

def z860 : W := mkw 0x09b801200f800220 0x026e004803e00088 0xbffc03fc0fc00fff 0xefff00ff03f003ff

def z861 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x4ffffc0003fff000 0xd3ffff0000fffc00

def z862 : W := mkw 0x030022c29a248dc0 0x00c008b0a6892370 0xff03e3c3fe3f8fc3 0xbfc0f8f0ff8fe3f0

def z863 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xdffffccc0ffff0cf 0xf7ffff3303fffc33

def z864 : W := mkw 0x4ddfd8000fdb66a8 0xd377f60003f6d9aa 0xfffffcfc0fffffff 0xffffff3f03ffffff

def z865 : W := mkw 0x6eefffff6041a045 0x1bbbffffd8106811 0xeffffffff3c388ff 0xfbfffffffcf0e23f

def z866 : W := mkw 0x00046c57e061b855 0x00011b15f8186e15 0xe00cfcfff3e3f8fe 0xf8033f3ffcf8fe3f

def z867 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x50f31f33fd3c7731 0x543cc7ccff4f1dcc

def z868 : W := mkw 0x066397b160000000 0x0198e5ec58000000 0x6ff31f33f0000003 0x5bfcc7ccfc000000

def z869 : W := mkw 0x6eefffff6041a045 0x1bbbffffd8106811 0xeffffffff3e3f0cf 0xfbfffffffcf8fc33

def z870 : W := mkw 0x08e9153120000000 0x023a454c48000000 0x6fff1f33f0000003 0xdbffc7ccfc000000

def z871 : W := mkw 0x6eefffff60412001 0x1bbbffffd8104800 0x6ffffffff023f003 0xdbfffffffc08fc00

def z872 : W := mkw 0x6eeb93a860000001 0x1bbae4ea18000000 0x6ff30303f0000003 0x1bfcc0c0fc000000

def z873 : W := mkw 0x6eefffff60001011 0x1bbbffffd8000404 0x6ffffffff1007033 0xdbfffffffc401c0c

def z874 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff03e303fc3f8f03 0x3fc0f8c0ff0fe3c0

def z875 : W := mkw 0x4ddfd8000fdb6228 0xd377f60003f6d88a 0xdffffc000ffff03f 0xf7ffff0003fffc0f

def z876 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0f31ff3ff3c7ff3 0xfc3cc7fcffcf1ffc

def z877 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x2ffc03fc03c00ffc 0xcbff00ff00f003ff

def z878 : W := mkw 0x09dd58000fc96000 0x0277560003f25800 0xdffffc000ffff003 0xf7ffff0003fffc00

def z879 : W := mkw 0x10711535b52c5b34 0x041c454d6d4b16cd 0xf0f31f3ffd3c7f3f 0x7c3cc7cfff4f1fcf

def z880 : W := mkw 0x10511000952c5b30 0x04144400254b16cc 0xf0f31f03fd3c7f33 0x7c3cc7c0ff4f1fcc

def z881 : W := mkw 0x0463953120000000 0x0118e54c48000000 0x6ff3ff33f0000003 0xdbfcffccfc000000

def z882 : W := mkw 0x7eefffff60001231 0x1fbbffffd800048c 0x6ffffffff0000033 0xdbfffffffc00000c

def z883 : W := mkw 0x6eefffff60413015 0x1bbbffffd8104c05 0x6ffffffff0007003 0xdbfffffffc001c00

def z884 : W := mkw 0x6ddfd8080fdb6008 0xdb77f60203f6d802 0xdffffc0c0ffff00f 0xf7ffff0303fffc03

def z885 : W := mkw 0x0643b2c240000000 0x0190ecb090000000 0x6ff3ffc3f0000003 0xdbfcfff0fc000000

def z886 : W := mkw 0x00046c579065b954 0x00011b15e4196e55 0xe00cfffff3e3fffe 0xf8033ffffcf8ffff

def z887 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0ff1f33fffc7f33 0xfc3fc7ccffff1fcc

def z888 : W := mkw 0x6eefffff60412001 0x1bbbffffd8104800 0xeffffffff3e3f8ff 0xfbfffffffcf8fe3f

def z889 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0xfffce3fc0fe38fff 0xffff38ff03f8e3ff

def z890 : W := mkw 0x4ccffc5760000001 0x1333ff15d8000000 0x4ff3fc03f0000001 0x13fcff00fc000000

def z891 : W := mkw 0x000468460041a044 0x00011a1180106811 0xe00cfcfc03e3f8fe 0xf8033f3f00f8fe3f

def z892 : W := mkw 0x811000009ff7bffc 0x6044000027fdefff 0x900000000ffffffc 0x2400000003ffffff

def z893 : W := mkw 0x00046c570041b054 0x00011b15c0106c15 0xa00cfcfc03c3f8fe 0xe8033f3f00f0fe3f

def z894 : W := mkw 0x6eebb3ea60000001 0x1bbaecfa98000000 0x6fffe3fff0000003 0xdbfff8fffc000000

def z895 : W := mkw 0x811000009fbecdc0 0xa044000027efb370 0x900000000e3f8fc0 0x24000000038fe3f0

def z896 : W := mkw 0x6eefffff60c12001 0x9bbbffffd8304800 0x6ffffffff0c00003 0xdbfffffffc300000

def z897 : W := mkw 0x2eaaa3ea40000000 0x0baaa8fa90000000 0x6ff3e3c3f0000003 0x9bfcf8f0fc000000

def z898 : W := mkw 0x0ddb90000f9a4000 0x0376e40003e69000 0xdffffc000ffff003 0xf7ffff0003fffc00

def z899 : W := mkw 0x4ddb90000f9a4000 0x9376e40003e69000 0xdff3fc000f3ff003 0xf7fcff0003cffc00

def z900 : W := mkw 0x2ae917b920000000 0x0aba45ee48000000 0x6ff31f33f0000003 0x5bfcc7ccfc000000

def z901 : W := mkw 0x2aed7fff20000000 0x0abb5fffc8000000 0x6ffffffff0000003 0xdbfffffffc000000

def z902 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xfffffcfc0ffff003 0xffffff3f03fffc00

def z903 : W := mkw 0x4ddfd8040fdb6004 0x9377f60103f6d801 0xdffffc0c0ffff00f 0xf7ffff0303fffc03

def z904 : W := mkw 0x6eebb7ff60000001 0x1bbaedffd8000000 0x2fff03fff0000003 0xcbffc0fffc000000

def z905 : W := mkw 0x811000009fb68fe8 0x6044000027eda3fa 0x900000000e3f8fc0 0x24000000038fe3f0

def z906 : W := mkw 0x099c48000fdb6000 0x8267120003f6d800 0xdffcfc000ffff003 0xf7ff3f0003fffc00

def z907 : W := mkw 0x4ceb953120000000 0x133ae54c48000000 0x6ff31f33f0000003 0x5bfcc7ccfc000000

def z908 : W := mkw 0x00044c1500413014 0x0001130540104c05 0xe00cfcfc03e3f8fe 0xf8033f3f00f8fe3f

def z909 : W := mkw 0x4ceffd7720000000 0x133bff5dc8000000 0x6ffffffff0000003 0xdbfffffffc000000

def z910 : W := mkw 0x0602a2c2d0248940 0x0180a8b0b4092250 0xff03e3c3fe3f8fc3 0xbfc0f8f0ff8fe3f0

def z911 : W := mkw 0x0667fff760000000 0x0199fffdd8000000 0x6ffffffff0000003 0xdbfffffffc000000

def z912 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xfffffcc00ffff8c3 0xffffff3003fffe30

def z913 : W := mkw 0x6eebb7ff60000001 0x1bbaedffd8000000 0x6ff3e3fff0000003 0x9bfcf8fffc000000

def z914 : W := mkw 0x30711539b52c5b38 0x4c1c454e6d4b16ce 0xf0f31f3ffd3c7f3f 0x7c3cc7cfff4f1fcf

def z915 : W := mkw 0x233027ff6f8006a9 0x48cc09ffdbe001aa 0xb00003ffffc00ffc 0x2c0000fffff003ff

def z916 : W := mkw 0x0b9802800f800480 0x02e600a003e00120 0xbffc03fc0fc00fff 0xefff00ff03f003ff

def z917 : W := mkw 0x4ccfd800005b6000 0x9333f6000016d800 0x4ff3fc00003ff001 0x13fcff00000ffc00

def z918 : W := mkw 0x6eaeefff60000001 0x1babbbffd8000000 0x2ffce3fff0000003 0xcbff38fffc000000

def z919 : W := mkw 0x00046c5700412000 0x00011b15c0104800 0xe00cfcff83e3f8fe 0xf8033f3fe0f8fe3f

def z920 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0f31ffffd3c7fff 0x7c3cc7ffff4f1fff

def z921 : W := mkw 0x6eefffff60000221 0x1bbbffffd8000088 0x6ffffffff0000f33 0xdbfffffffc0003cc

def z922 : W := mkw 0x2aa807b920000000 0x0aaa01ee48000000 0x2ffc03fff0000003 0xcbff00fffc000000

def z923 : W := mkw 0x00046c579065b954 0x00011b15e4196e55 0xf00cfcff8ffffffe 0xfc033f3fe3ffffff

def z924 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x4fffff3ff0000001 0x53ffffcffc000000

def z925 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x6ff3fffff0000001 0x1bfcfffffc000000

def z926 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x6ffffffff1c0003f 0xdbfffffffc70000f

def z927 : W := mkw 0x6eefffff601a4001 0x9bbbffffd8069000 0x6ffffffff01c0003 0xdbfffffffc070000

def z928 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x30f31f33fd1c7f31 0x4c3cc7ccff471fcc

def z929 : W := mkw 0x811000009f368fe0 0x2044000027cda3f8 0x900000000f3f8ff0 0x2400000003cfe3fc

def z930 : W := mkw 0x10711531350c5330 0x041c454c4d4314cc 0x70f31f33fd1c7733 0x5c3cc7ccff471dcc

def z931 : W := mkw 0x00046c570041b054 0x00011b15c0106c15 0xc00cfcfc03e3f0fe 0xf0033f3f00f8fc3f

def z932 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x6ffffffff2c000cf 0xdbfffffffcb00033

def z933 : W := mkw 0x4cdfd800055b6000 0x9337f6000156d800 0xdffffc000d3ff003 0xf7ffff00034ffc00

def z934 : W := mkw 0x2bb803a80f8006a8 0x4aee00ea03e001aa 0x3ffc03fc0ec00ffd 0x8fff00ff03b003ff

def z935 : W := mkw 0x033003a00f0006a0 0x00cc00e803c001a8 0xbffc03fc0fc00fff 0xefff00ff03f003ff

def z936 : W := mkw 0x00046c570041b054 0x00011b15c0106c15 0x600cfcff83c3f0fe 0xd8033f3fe0f0fc3f

def z937 : W := mkw 0x4ddfd8000fdb6488 0xd377f60003f6d922 0xdffffc000ffff0cf 0xf7ffff0003fffc33

def z938 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x6ff3ff33f0000003 0x5bfcffccfc000000

def z939 : W := mkw 0x6eefffff60412005 0x1bbbffffd8104801 0x6ffffffff0c0000f 0xdbfffffffc300003

def z940 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xdffffc000ffff8ff 0xf7ffff0003fffe3f

def z941 : W := mkw 0x6eeffbea60000001 0x1bbbfefa98000000 0x6fffffc3f0000003 0xdbfffff0fc000000

def z942 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0xfffffffffc000f03 0xffffffffff0003c0

def z943 : W := mkw 0x4ceffd7760000001 0x133bff5dd8000000 0x6fffff33f0000003 0xdbffffccfc000000

def z944 : W := mkw 0x4557fc576fdb6001 0x9155ff15dbf6d800 0xd003fc03fffff000 0x3400ff00fffffc00

def z945 : W := mkw 0x2ab803a8058006a8 0x4aae00ea016001aa 0x2ffc03fc01c00fff 0xcbff00ff007003ff

def z946 : W := mkw 0x10711531b52cdb70 0x041c454c6d4b36dc 0xf0f31f33ff3ffff3 0x7c3cc7ccffcffffc

def z947 : W := mkw 0x6eefffff60000481 0x1bbbffffd8000120 0x6ffffffff0000fc3 0xdbfffffffc0003f0

def z948 : W := mkw 0x922027f7f0249ff4 0x248809fdfc0927fd 0x200003fff0000ffc 0x080000fffc0003ff

def z949 : W := mkw 0x0e8aa2c240000000 0x03a2a8b090000000 0x6fffe3c3f0000003 0xdbfff8f0fc000000

def z950 : W := mkw 0x111000009f2c5fb0 0x0444000027cb17ec 0x900000000f3c7ff0 0x2400000003cf1ffc

def z951 : W := mkw 0x6eefffff60001015 0x1bbbffffd8000405 0x6ffffffff000003f 0xdbfffffffc00000f

def z952 : W := mkw 0x10046c57b065b954 0x04011b15ec196e55 0xe00cfcfff3e3f8fe 0xf8033f3ffcf8fe3f

def z953 : W := mkw 0x6eebb3ea60000001 0x1bbaecfa98000000 0x4ff3e303f0000001 0x13fcf8c0fc000000

def z954 : W := mkw 0x911000009f7ffff4 0x2444000027dffffd 0x900000000ffffffc 0x2400000003ffffff

def z955 : W := mkw 0x6eebb7ff60000001 0x1bbaedffd8000000 0x6ff31ffff0000003 0x5bfcc7fffc000000

def z956 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x4fffff03f0000003 0xd3ffffc0fc000000

def z957 : W := mkw 0xbffb93a87f9e47a8 0x6ffee4ea1fe791ea 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z958 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x5f03e3c3fe3f87c1 0x97c0f8f0ff8fe1f0

def z959 : W := mkw 0x78fd5d3d25497235 0x1e3f574f49525c8d 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z960 : W := mkw 0xa22027fff0249dd5 0x288809fffc092775 0x200003fff0000ffc 0x080000fffc0003ff

def z961 : W := mkw 0x811000009fffe940 0xa044000027fffa50 0x900000000ffff000 0x2400000003fffc00

def z962 : W := mkw 0x6eefffff60413015 0x1bbbffffd8104c05 0xeffffffff3e3f03f 0xfbfffffffcf8fc0f

def z963 : W := mkw 0x38fd5d3d25c9723c 0x4e3f574f49725c8f 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z964 : W := mkw 0x7eefffff60085011 0x1fbbffffd8021404 0x6ffffffff0007003 0xdbfffffffc001c00

def z965 : W := mkw 0xeeefffff600084c1 0x3bbbffffd8002130 0x6ffffffff00000c3 0xdbfffffffc000030

def z966 : W := mkw 0x00711531b52c4900 0x001c454c6d4b1240 0xf0f31f33fd3c7f03 0x7c3cc7ccff4f1fc0

def z967 : W := mkw 0xef8eeace4a53a4c5 0x3be3bab39294e931 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z968 : W := mkw 0x6eeb97b960000001 0x1bbae5ee58000000 0x2ff30333f0000001 0x0bfcc0ccfc000000

def z969 : W := mkw 0x4ccff84240000000 0x1333fe1090000000 0x4ffffc03f0000003 0xd3ffff00fc000000

def z970 : W := mkw 0x5447fc57f06df955 0x1511ff15fc1b7e55 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z971 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0xeffffffff3c00003 0xfbfffffffcf00000

def z972 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xffffff000fffff03 0xffffffc003ffffc0

def z973 : W := mkw 0x4ddfd8000f1a4000 0x1377f60003c69000 0xdffffc000f3ff003 0xf7ffff0003cffc00

def z974 : W := mkw 0x8702a2c2da369dd0 0x21c0a8b0b68da774 0xff03e3c3ff3ffff3 0xbfc0f8f0ffcffffc

def z975 : W := mkw 0x6ffb93a86f9a46a9 0xdbfee4ea1be691aa 0x1ff303007c1c0701 0x07fcc0c01f0701c0

def z976 : W := mkw 0x10511411b52c5910 0x041445046d4b1644 0xf0f31f03fd3c7f03 0x7c3cc7c0ff4f1fc0

def z977 : W := mkw 0x6eefdfbd60000001 0x1bbbf7ef58000000 0x6fff1f3ff0000003 0x5bffc7cffc000000

def z978 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x70f31f33fc3c7f31 0x1c3cc7ccff0f1fcc

def z979 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0xeffffffff2238003 0xfbfffffffc88e000

def z980 : W := mkw 0x2eebb7fb60000000 0x0bbaedfed8000000 0x6ffffffff0000003 0xdbfffffffc000000

def z981 : W := mkw 0x911000009ffffff0 0xa444000027fffffc 0x900000000ffffff0 0x2400000003fffffc

def z982 : W := mkw 0x811000009fb68dc0 0x2044000027eda370 0x900000000fff8fc0 0x2400000003ffe3f0

def z983 : W := mkw 0x4ecffed760000001 0x13b3ffb5d8000000 0x6fffffc3f0000003 0xdbfffff0fc000000

def z984 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x6ffffffff00008ff 0xdbfffffffc00023f

def z985 : W := mkw 0xb22027fbf0249ff8 0x6c8809fefc0927fe 0x200003fff0000ffc 0x080000fffc0003ff

def z986 : W := mkw 0x78fd5d3d25c97231 0x9e3f574f49725c8c 0x00fc1c3c01c07030 0x403f070f00701c0c

def z987 : W := mkw 0x10611531b02c5910 0x0418454c6c0b1644 0xf0f31f33fc3c7f03 0x7c3cc7ccff0f1fc0

def z988 : W := mkw 0x000448008061b854 0x0001120020186e15 0xe00cfcfc03e3f8fe 0xf8033f3f00f8fe3f

def z989 : W := mkw 0x2ab803a805000220 0x0aae00ea01400088 0xbffc03fc0fc00fff 0xefff00ff03f003ff

def z990 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xf0ff1ffffd3c7f33 0xfc3fc7ffff4f1fcc

def z991 : W := mkw 0x8602a2c2d0368940 0x2180a8b0b40da250 0xff03e3c3fc3f8f03 0xbfc0f8f0ff0fe3c0

def z992 : W := mkw 0xef8eeace4ad3a4c1 0xbbe3bab392b4e930 0x0f0ce0cc02c380c0 0x83c3383300b0e030

def z993 : W := mkw 0x070282809a360d80 0x01c0a0a0268d8360 0xff03e3c3fe3f8fc3 0xbfc0f8f0ff8fe3f0

def z994 : W := mkw 0x8702a2c25a1685c0 0x21c0a8b09685a170 0x7f03e3c3fe1f87c3 0x9fc0f8f0ff87e1f0

def z995 : W := mkw 0x58fd5d3525c97234 0x963f574d49725c8d 0x00fc1c3c01c0703c 0x403f070f00701c0f

def z996 : W := mkw 0x4ccfdc1120000000 0x1333f70448000000 0x4ffffc03f0000003 0xd3ffff00fc000000

def z997 : W := mkw 0x000468428061a840 0x00011a10a0186a10 0xe00cfcff83e3f8fe 0xf8033f3fe0f8fe3f

def z998 : W := mkw 0x811000009fa48fe8 0x6044000027e923fa 0x900000000fc00ffc 0x2400000003f003ff

def z999 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0x70f31f33fc3c7703 0x5c3cc7ccff0f1dc0

def z1000 : W := mkw 0xa702a2cada368dc8 0x69c0a8b2b68da372 0xff03e3cffe3f8fcf 0xbfc0f8f3ff8fe3f3

def z1001 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xd0f31f03fd3c7f31 0x343cc7c0ff4f1fcc

def z1002 : W := mkw 0x00611531b0241910 0x0018454c6c090644 0xf0f31f33fd3c7f33 0x7c3cc7ccff4f1fcc

def z1003 : W := mkw 0x0663b3e260000000 0x0198ecf898000000 0x6ff3e3c3f0000003 0x9bfcf8f0fc000000

def z1004 : W := mkw 0xeeefffff60128041 0x3bbbffffd804a010 0x6ffffffff0038003 0xdbfffffffc00e000

def z1005 : W := mkw 0x6eefffff60084001 0x1bbbffffd8021000 0x6ffffffff03c7003 0xdbfffffffc0f1c00

def z1006 : W := mkw 0x4dcfd8000a5b6000 0x9373f6000296d800 0xdffffc000e3ff003 0xf7ffff00038ffc00

def z1007 : W := mkw 0x6eefffff600006a9 0x5bbbffffd80001aa 0x6ffffffff0000703 0xdbfffffffc0001c0

def z1008 : W := mkw 0x911000009f3e5fb0 0x2444000027cf97ec 0x900000000d3c7f30 0x24000000034f1fcc

def z1009 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0x7f03e3c3fc3f8fc1 0x1fc0f8f0ff0fe3f0

def z1010 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0xeffffffff1000833 0xfbfffffffc40020c

def z1011 : W := mkw 0x4ddfd8000fdb6220 0x9377f60003f6d888 0xdffffc000fffff33 0xf7ffff0003ffffcc

def z1012 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0xeffffffff1207003 0xfbfffffffc481c00

def z1013 : W := mkw 0x2ba803a80a8006a8 0x4aea00ea02a001aa 0x2ffc03fc02c00fff 0xcbff00ff00b003ff

def z1014 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0xeffffffff20008c3 0xfbfffffffc800230

def z1015 : W := mkw 0x6eefffff60412001 0x1bbbffffd8104800 0x6ffffffff1c07003 0xdbfffffffc701c00

def z1016 : W := mkw 0x811000009f3ecdc0 0x2044000027cfb370 0x900000000f3fffc0 0x2400000003cffff0

def z1017 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x9ffcfc000ffff000 0xe7ff3f0003fffc00

def z1018 : W := mkw 0x6eefffff60120001 0x1bbbffffd8048000 0x6ffffffff03f8003 0xdbfffffffc0fe000

def z1019 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x5ffffc000efff001 0x97ffff0003bffc00

def z1020 : W := mkw 0x10711531b52c5b30 0x041c454c6d4b16cc 0xd0f31f03fd3c7703 0x743cc7c0ff4f1dc0

def z1021 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0x5ffffc000dfff001 0x57ffff00037ffc00

def z1022 : W := mkw 0xc447fc57d07ff954 0xb111ff15f41ffe55 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z1023 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x2ffcfffff0000000 0xcbff3ffffc000000

def z1024 : W := mkw 0x911000009fbedff8 0x6444000027efb7fe 0x900000000ffffffc 0x2400000003ffffff

def z1025 : W := mkw 0x00711120952c4b20 0x001c4448254b12c8 0xf0f31f33fd3c7f33 0x7c3cc7ccff4f1fcc

def z1026 : W := mkw 0x6eefffff60000001 0x1bbbffffd8000000 0x2fffe3fff0000001 0x8bfff8fffc000000

def z1027 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xdff3fc000ffff001 0x37fcff0003fffc00

def z1028 : W := mkw 0xcf8eeac64ad3a4c4 0xb3e3bab192b4e931 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z1029 : W := mkw 0x6eeb97b960000001 0x1bbae5ee58000000 0x4ff31f03f0000001 0x13fcc7c0fc000000

def z1030 : W := mkw 0x2aa823ea40000000 0x0aaa08fa90000000 0x2ffc03fff0000003 0xcbff00fffc000000

def z1031 : W := mkw 0x8702a2c2da368dc0 0x21c0a8b0b68da370 0xff03e3fffe3f8fff 0xbfc0f8ffff8fe3ff

def z1032 : W := mkw 0x6eefffff60000229 0x5bbbffffd800008a 0x6ffffffff000003f 0xdbfffffffc00000f

def z1033 : W := mkw 0xaf8eeace4ad3a4cc 0x6be3bab392b4e933 0x0f0ce0cc02c380cc 0x83c3383300b0e033

def z1034 : W := mkw 0x111000009fff7fb8 0xc444000027ffdfee 0x900000000ffffffc 0x2400000003ffffff

def z1035 : W := mkw 0x4ddfd8000fdb6000 0x9377f60003f6d800 0xffffff03fffff003 0xffffffc0fffffc00

def z1036 : W := mkw 0x099800000f8006a8 0x4266000003e001aa 0xbffc00fc0fc00fff 0xefff003f03f003ff

def z1037 : W := mkw 0x811000009ffffdd4 0xa044000027ffff75 0x900000000ffffffc 0x2400000003ffffff

def z1038 : W := mkw 0xc447fc57f077b955 0x3111ff15fc1dee55 0x4003fc03f03ff000 0x1000ff00fc0ffc00

def z1039 : W := mkw 0x6aed5fbd20000001 0x1abb57ef48000000 0x6fff1ffff0000003 0xdbffc7fffc000000

def z1040 : W := mkw 0x00046c578061b854 0x00011b15e0186e15 0xf00ffcff8ffff8ff 0xfc03ff3fe3fffe3f

def z1041 : W := mkw 0x4cdfd80005db6000 0x9337f6000176d800 0x4ffffc0001fff003 0xd3ffff00007ffc00

def z1042 : W := mkw 0x2bb803a80f9206a8 0x4aee00ea03e481aa 0xbffc03fc0fff8fff 0xefff00ff03ffe3ff

def z1043 : W := mkw 0x0702a2c2da360900 0x01c0a8b0b68d8240 0xff03e3c3fe3f8f03 0xbfc0f8f0ff8fe3c0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z8]),(0,[z0,z9,z2,z3,z4,z5,z10])],[(0,[z0,z11,z2,z3,z4,z12,z6]),(0,[z13,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z14,z4,z5,z6]),(0,[z0,z15,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z16])],[(0,[z0,z2,z3,z4,z5,z6,z17]),(0,[z0,z18,z19,z3,z4,z5,z6]),(0,[z0,z20,z9,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z21,z5,z6]),(0,[z0,z2,z3,z22,z4,z5,z6]),(0,[z23,z0,z2,z3,z4,z5,z6])],[(0,[z24,z0,z2,z3,z25,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z26]),(0,[z0,z2,z3,z27,z4,z6,z28])],[(0,[z0,z29,z3,z4,z21,z5,z6]),(0,[z0,z2,z30,z3,z5,z31,z6]),(0,[z0,z2,z32,z3,z4,z5,z6])],[(0,[z0,z33,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z34,z5,z6]),(0,[z35,z0,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z36,z6]),(0,[z0,z2,z37,z3,z38,z4,z6])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z2,z39,z3,z4,z5,z6]),(0,[z0,z40,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z41,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z42,z6]),(0,[z0,z2,z3,z4,z5,z6,z43]),(0,[z0,z44,z11,z2,z3,z4,z6]),(0,[z0,z2,z45,z3,z4,z5,z6]),(0,[z0,z2,z3,z46,z47,z4,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z48,z6]),(0,[z0,z49,z2,z3,z4,z50,z6])],[(0,[z0,z51,z18,z3,z4,z5,z6]),(1,[z52,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z53]),(0,[z0,z54,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z50,z6,z55])],[(0,[z0,z2,z3,z4,z56,z5,z6])],[(0,[z0,z2,z57,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z47,z5,z6]),(0,[z0,z2,z3,z4,z5,z58,z6])],[(0,[z0,z59,z2,z3,z4,z5,z6]),(0,[z60,z0,z2,z3,z4,z5,z6]),(0,[z0,z44,z3,z4,z5,z61,z6]),(1,[z0,z11,z2,z3,z4,z55])],[(0,[z0,z2,z3,z4,z5,z6,z62]),(0,[z0,z2,z63,z3,z4,z5,z6]),(0,[z0,z64,z2,z3,z4,z5,z6]),(0,[z65,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z66,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z67])],[(0,[z68,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z69,z6]),(0,[z0,z2,z3,z4,z5,z6,z70]),(0,[z0,z2,z3,z47,z5,z31,z6])],[(0,[z0,z2,z3,z71,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z72,z6]),(0,[z0,z2,z3,z73,z4,z5,z6]),(0,[z0,z51,z2,z19,z4,z5,z6]),(0,[z0,z74,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z75])]],
   [[(0,[z0,z76,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z77,z6]),(0,[z78,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z21,z5,z61,z6])],[(0,[z0,z2,z79,z3,z4,z5,z6]),(0,[z80,z0,z2,z3,z4,z5,z81]),(0,[z0,z2,z82,z3,z4,z83,z6]),(0,[z0,z2,z3,z4,z84,z5,z6]),(1,[z0,z15,z2,z30,z3,z6])],[(0,[z85,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z86,z3,z4,z5,z6]),(0,[z87,z0,z2,z3,z4,z88,z6]),(0,[z0,z2,z3,z4,z5,z6,z89]),(0,[z90,z0,z2,z3,z4,z5,z6])],[(0,[z24,z2,z3,z91,z4,z5,z6]),(0,[z0,z44,z2,z3,z4,z88,z6]),(0,[z0,z2,z3,z4,z5,z92,z6]),(1,[z0,z2,z93,z3,z4,z6])],[(0,[z0,z2,z3,z94,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z95,z6]),(0,[z0,z96,z2,z3,z4,z5,z6])],[(0,[z97,z0,z2,z3,z4,z5,z6]),(0,[z0,z98,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z99,z6])],[(0,[z0,z2,z3,z4,z5,z100,z6]),(0,[z0,z2,z3,z4,z101,z5,z6]),(0,[z0,z2,z4,z5,z102,z6,z28]),(0,[z0,z2,z3,z103,z4,z5,z6])]],
   [[(0,[z104,z2,z86,z3,z4,z5,z6]),(0,[z105,z0,z2,z3,z4,z106,z6]),(0,[z0,z2,z30,z3,z4,z88,z6]),(0,[z0,z2,z107,z3,z4,z5,z6])],[(0,[z0,z2,z3,z91,z4,z5,z6]),(0,[z0,z2,z3,z4,z108,z5,z6]),(0,[z0,z109,z2,z4,z5,z6,z28])],[(0,[z110,z0,z111,z3,z4,z5,z6]),(0,[z0,z2,z112,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z113,z6]),(0,[z0,z2,z114,z3,z4,z5,z6]),(0,[z0,z2,z3,z115,z4,z5,z6]),(0,[z0,z116,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z117]),(0,[z0,z2,z3,z4,z118,z5,z6])],[],[(0,[z119,z2,z86,z3,z4,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z120]),(0,[z0,z2,z3,z91,z5,z121,z6]),(0,[z0,z2,z3,z122,z4,z5,z6]),(0,[z0,z2,z3,z123,z4,z5,z6]),(1,[z0,z2,z3,z4,z6,z124]),(0,[z125,z0,z2,z3,z4,z5,z6])],[(0,[z24,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z126,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z88,z50,z6]),(0,[z0,z51,z3,z127,z4,z5,z6])],[(0,[z0,z2,z3,z46,z4,z12,z6]),(0,[z0,z2,z3,z128,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z129,z6]),(0,[z0,z2,z130,z3,z4,z131,z6])],[(1,[z0,z2,z3,z4,z132,z6]),(0,[z0,z2,z3,z4,z5,z133,z6]),(0,[z0,z2,z3,z4,z5,z134,z6]),(0,[z0,z2,z3,z4,z5,z6,z135])],[(0,[z0,z2,z3,z4,z5,z136,z6]),(0,[z0,z2,z3,z4,z137,z5,z6]),(0,[z0,z2,z138,z4,z5,z121,z6]),(0,[z0,z139,z3,z4,z5,z6,z10]),(0,[z0,z140,z2,z3,z4,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z141]),(0,[z0,z2,z3,z38,z4,z5,z6]),(0,[z0,z2,z3,z4,z142,z5,z6])],[(0,[z143,z0,z2,z3,z4,z5,z6]),(0,[z105,z0,z119,z3,z4,z5,z6]),(0,[z0,z144,z2,z3,z4,z5,z6]),(0,[z0,z2,z145,z3,z4,z5,z6]),(0,[z0,z49,z2,z3,z4,z83,z6]),(0,[z0,z2,z3,z4,z146,z6,z28]),(0,[z0,z2,z3,z4,z147,z50,z6])],[(0,[z148,z0,z2,z3,z4,z5,z6]),(0,[z110,z0,z2,z3,z149,z5,z6]),(0,[z2,z3,z4,z12,z5,z88,z6]),(0,[z0,z2,z3,z150,z4,z5,z6]),(0,[z0,z151,z2,z3,z4,z5,z6])],[(0,[z0,z152,z2,z3,z4,z5,z6]),(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z0,z2,z154,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z155,z6])],[(0,[z0,z2,z3,z4,z5,z156,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z157,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z158,z5,z6]),(0,[z0,z2,z3,z159,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z160]),(0,[z0,z2,z3,z4,z161,z6,z10])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z162]),(0,[z104,z0,z2,z3,z4,z5,z6]),(0,[z104,z0,z2,z3,z4,z5,z163]),(0,[z0,z2,z3,z4,z5,z164,z6]),(0,[z0,z165,z2,z3,z4,z5,z6])],[(0,[z0,z166,z2,z3,z4,z5,z6])],[(0,[z0,z111,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z167,z6]),(0,[z168,z0,z2,z3,z4,z5,z6]),(0,[z0,z169,z2,z3,z4,z5,z6]),(0,[z0,z170,z2,z3,z4,z5,z6]),(0,[z0,z171,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z172,z5,z173]),(0,[z0,z11,z2,z3,z4,z147,z6])],[(0,[z174,z0,z119,z3,z4,z5,z6]),(0,[z0,z2,z175,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z176,z6]),(0,[z177,z0,z2,z3,z4,z5,z6]),(0,[z0,z178,z2,z3,z4,z5,z6])],[(0,[z0,z179,z2,z3,z4,z5,z6]),(0,[z0,z180,z2,z3,z5,z173,z6]),(0,[z0,z2,z181,z4,z5,z102,z6]),(0,[z0,z11,z2,z3,z47,z4,z6])],[(0,[z0,z2,z3,z4,z5,z182,z6]),(0,[z0,z2,z3,z183,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z83,z6]),(0,[z0,z2,z3,z4,z5,z184,z6])],[(0,[z185,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z186,z6]),(0,[z0,z2,z3,z4,z5,z6,z187]),(0,[z188,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z189,z5,z6]),(0,[z0,z15,z2,z3,z4,z50,z6]),(0,[z190,z0,z2,z3,z4,z5,z6]),(0,[z0,z191,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z192,z4,z5,z6]),(0,[z0,z2,z3,z193,z4,z5,z6]),(0,[z194,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z195,z6]),(0,[z0,z2,z3,z4,z5,z6,z196]),(0,[z0,z2,z3,z197,z4,z5,z6]),(0,[z0,z2,z3,z47,z4,z31,z6])],[(0,[z0,z198,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z199]),(0,[z0,z2,z3,z4,z5,z6,z200])],[(0,[z0,z2,z3,z4,z201,z5,z6]),(0,[z0,z2,z202,z3,z4,z5,z6]),(0,[z0,z29,z2,z3,z4,z88,z6]),(1,[z0,z2,z3,z4,z203,z6]),(0,[z0,z204,z2,z3,z4,z5,z6]),(0,[z0,z9,z2,z3,z4,z5,z173])],[(0,[z205,z0,z2,z3,z4,z5,z6]),(0,[z206,z0,z2,z3,z4,z5,z6]),(0,[z0,z20,z3,z4,z131,z5,z6]),(0,[z0,z207,z2,z3,z4,z5,z6]),(0,[z0,z44,z15,z2,z3,z4,z6])],[(1,[z87,z2,z3,z4,z12,z6])],[(1,[z0,z51,z127,z4,z5,z6]),(0,[z0,z208,z2,z3,z4,z5,z6]),(1,[z35,z0,z3,z4,z5,z209]),(0,[z0,z2,z3,z4,z210,z5,z6])],[(0,[z0,z2,z3,z211,z4,z5,z6]),(0,[z0,z2,z3,z212,z4,z5,z6]),(0,[z0,z11,z29,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z10])],[(0,[z105,z119,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z213])]],
   [[(0,[z214,z0,z2,z3,z4,z5,z6]),(0,[z35,z0,z2,z3,z172,z4,z5])],[(1,[z174,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z215,z131,z5])],[(0,[z105,z0,z2,z3,z4,z216,z6]),(0,[z0,z2,z3,z4,z88,z83,z6]),(0,[z0,z2,z3,z4,z203,z5,z6]),(0,[z0,z2,z19,z3,z4,z5,z6]),(1,[z0,z170,z3,z4,z5,z164]),(0,[z0,z217,z2,z3,z138,z5,z6]),(0,[z0,z2,z3,z218,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z219])],[(0,[z0,z2,z37,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z220,z5,z6]),(0,[z221,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z222,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z223]),(0,[z0,z224,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z225,z4,z5,z6])],[(0,[z226,z0,z2,z3,z4,z5,z6]),(0,[z0,z227,z2,z3,z4,z5,z6]),(1,[z0,z44,z3,z4,z61,z6])],[(0,[z0,z18,z2,z19,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z36,z6])]],
   [[(0,[z0,z228,z2,z3,z4,z5,z6]),(1,[z229,z2,z3,z4,z88,z6]),(1,[z0,z180,z3,z230,z5,z6]),(0,[z0,z2,z37,z3,z5,z121,z6]),(0,[z0,z231,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z232])],[(0,[z0,z2,z233,z3,z4,z5,z6]),(0,[z0,z2,z3,z234,z4,z5,z6]),(0,[z0,z20,z180,z3,z4,z5,z6]),(0,[z0,z180,z2,z3,z230,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z235]),(0,[z236,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z237,z6])],[(0,[z0,z86,z3,z127,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z238]),(0,[z0,z2,z239,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z240,z5,z6]),(0,[z0,z2,z3,z241,z4,z5,z6])],[(0,[z242,z2,z79,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z243]),(0,[z0,z20,z2,z3,z4,z5,z6]),(1,[z244,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z245,z4,z5,z6]),(0,[z0,z246,z2,z3,z4,z5,z6]),(0,[z0,z2,z247,z3,z4,z5,z6]),(0,[z0,z2,z3,z248,z4,z5,z6])],[(0,[z249,z0,z2,z3,z4,z5,z6]),(0,[z0,z250,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z251,z4,z5,z6])],[(0,[z242,z0,z2,z79,z4,z5,z6]),(0,[z252,z0,z2,z3,z4,z5,z6])],[(1,[z0,z253,z2,z3,z4,z5]),(0,[z0,z11,z2,z82,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z254,z6])]],
   [[(0,[z0,z2,z255,z3,z4,z5,z6]),(0,[z0,z2,z3,z256,z4,z5,z6]),(0,[z0,z257,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z258,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z259]),(0,[z0,z2,z3,z4,z5,z260,z6]),(0,[z0,z261,z2,z3,z4,z5,z6])],[(0,[z2,z86,z3,z4,z5,z6,z163]),(0,[z0,z262,z2,z3,z4,z5,z6]),(0,[z24,z263,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z264,z5,z6]),(0,[z229,z0,z2,z3,z4,z5,z6]),(1,[z0,z18,z19,z4,z5,z6])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z265,z4,z5,z6]),(0,[z266,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z267,z3,z4,z5,z6]),(0,[z0,z2,z3,z268,z4,z5,z6]),(0,[z35,z0,z20,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z4,z83,z6]),(0,[z0,z2,z3,z4,z269,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z270]),(0,[z110,z0,z2,z3,z4,z271,z6]),(0,[z272,z0,z2,z3,z4,z5,z6]),(0,[z0,z273,z2,z3,z4,z5,z6])],[(0,[z0,z2,z274,z3,z4,z5,z6]),(1,[z0,z2,z3,z275,z4,z6]),(0,[z0,z2,z3,z4,z276,z5,z6]),(0,[z0,z2,z277,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z278,z6]),(0,[z0,z2,z3,z4,z5,z121,z6]),(0,[z0,z49,z2,z82,z4,z5,z6])],[(0,[z0,z2,z30,z3,z138,z5,z6]),(0,[z0,z279,z2,z3,z4,z5,z6])],[(0,[z0,z2,z280,z3,z4,z5,z6]),(0,[z281,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z282,z6])]],
   [[(0,[z0,z283,z2,z3,z4,z5,z6]),(0,[z0,z284,z2,z3,z4,z5,z6]),(0,[z0,z2,z285,z3,z4,z5,z6])],[(0,[z0,z2,z3,z286,z4,z5,z6]),(0,[z0,z287,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z120,z6]),(0,[z0,z2,z3,z288,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z289,z6]),(0,[z0,z2,z290,z3,z4,z5,z6]),(1,[z0,z2,z3,z27,z4,z6]),(0,[z291,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z172,z4,z5,z173])],[(0,[z105,z0,z2,z3,z4,z5,z6]),(0,[z292,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z293,z3,z4,z5,z6]),(0,[z0,z180,z2,z3,z131,z5,z6]),(0,[z0,z2,z3,z294,z4,z5,z6])],[(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z50,z6])],[(0,[z295,z0,z2,z3,z4,z5,z6]),(0,[z0,z51,z2,z127,z4,z5,z6]),(1,[z0,z2,z130,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z296])],[(0,[z0,z2,z3,z297,z4,z5,z6]),(0,[z298,z0,z2,z3,z4,z5,z6])],[(0,[z299,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z300,z4,z5,z6]),(0,[z0,z301,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z302]),(0,[z0,z303,z2,z3,z4,z5,z6])]],
   [[(0,[z80,z2,z3,z4,z5,z6,z163]),(0,[z0,z2,z304,z3,z4,z5,z6]),(0,[z0,z217,z2,z4,z5,z121,z6]),(0,[z244,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z305,z5,z6]),(0,[z0,z2,z3,z4,z306,z5,z6])],[(0,[z307,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z308,z5,z6]),(1,[z0,z2,z37,z138,z5,z6]),(0,[z0,z2,z3,z4,z5,z309,z6])],[(0,[z0,z2,z3,z310,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z311,z6]),(0,[z0,z2,z3,z4,z312,z5,z6]),(0,[z0,z2,z3,z4,z313,z5,z6])],[(0,[z314,z0,z2,z3,z4,z5,z6]),(0,[z315,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z316,z6])],[(0,[z0,z51,z2,z3,z4,z5,z6])],[(0,[z0,z18,z119,z3,z4,z5,z6]),(0,[z110,z2,z3,z317,z4,z5,z6]),(1,[z242,z2,z79,z4,z5,z6]),(0,[z0,z170,z2,z3,z172,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z318]),(0,[z319,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z320]),(0,[z0,z321,z2,z3,z4,z5,z6])],[(0,[z0,z322,z2,z3,z4,z5,z6]),(0,[z0,z323,z2,z3,z4,z5,z6]),(0,[z0,z324,z2,z3,z4,z5,z6]),(1,[z104,z2,z3,z4,z5,z81])],[(0,[z0,z2,z325,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z326,z5,z6]),(0,[z0,z2,z181,z3,z4,z5,z28]),(0,[z0,z327,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z6,z55])]],
   [[(0,[z0,z2,z328,z3,z4,z5,z6]),(0,[z0,z2,z82,z3,z46,z4,z6]),(0,[z0,z329,z2,z3,z4,z5,z6])],[(0,[z110,z242,z2,z3,z4,z5,z6]),(0,[z0,z330,z2,z3,z4,z5,z6]),(1,[z0,z2,z82,z4,z83,z6]),(0,[z0,z2,z331,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z332,z5,z6]),(0,[z0,z2,z3,z4,z333,z5,z6]),(0,[z0,z2,z334,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z335,z5,z6]),(0,[z0,z336,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z337,z4,z5,z6])],[(0,[z338,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z5,z6,z339]),(0,[z0,z2,z3,z172,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z155,z6]),(0,[z0,z2,z3,z340,z4,z5,z6])],[(0,[z0,z44,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z341,z4,z5,z6]),(0,[z0,z2,z342,z3,z4,z5,z6]),(0,[z0,z217,z2,z37,z4,z5,z6])],[(1,[z0,z111,z3,z4,z5,z6]),(0,[z2,z79,z3,z317,z4,z5,z6]),(0,[z343,z0,z2,z3,z4,z5,z6]),(0,[z344,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z172,z5,z173,z6]),(0,[z345,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z346,z4,z5,z6]),(0,[z0,z2,z3,z347,z4,z5,z6]),(0,[z35,z52,z2,z3,z4,z5,z6]),(0,[z0,z348,z2,z3,z4,z5,z6]),(0,[z0,z349,z2,z3,z4,z5,z6])],[(0,[z0,z350,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z351,z4,z5,z6]),(0,[z352,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z30,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z120]),(0,[z353,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z354]),(0,[z0,z2,z3,z355,z4,z5,z6]),(0,[z356,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z357,z6])],[(0,[z104,z105,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z358]),(0,[z0,z2,z3,z4,z5,z81,z6]),(0,[z0,z359,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z61,z6]),(0,[z0,z15,z29,z2,z3,z4,z6]),(0,[z0,z360,z2,z3,z4,z5,z6]),(0,[z0,z361,z2,z3,z4,z5,z6])],[(0,[z0,z362,z2,z3,z4,z5,z6]),(0,[z0,z363,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z364,z5,z6]),(1,[z0,z360,z2,z3,z4,z6]),(0,[z0,z2,z3,z365,z4,z5,z6])],[(0,[z0,z366,z2,z3,z4,z5,z6]),(0,[z0,z109,z2,z3,z4,z5,z28]),(1,[z0,z2,z3,z4,z146,z6]),(1,[z0,z2,z3,z47,z31,z6])],[(0,[z0,z2,z3,z4,z12,z31,z6]),(0,[z0,z44,z2,z3,z4,z21,z6]),(0,[z0,z2,z3,z4,z367,z5,z6]),(0,[z0,z2,z3,z4,z6,z124,z209])],[(1,[z368,z2,z3,z4,z5,z6]),(0,[z0,z369,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z38,z4,z6])]],
   [[(0,[z110,z0,z2,z3,z4,z308,z6]),(0,[z0,z2,z370,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z371,z5,z6])],[(0,[z0,z2,z3,z372,z4,z5,z6]),(0,[z0,z2,z373,z3,z4,z5,z6]),(0,[z0,z374,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z375,z4,z5,z6])],[(1,[z0,z2,z3,z149,z5,z6]),(0,[z0,z2,z3,z376,z4,z5,z6]),(0,[z0,z49,z2,z3,z46,z4,z6])],[(0,[z0,z377,z2,z3,z4,z5,z6]),(0,[z0,z378,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z379]),(0,[z0,z3,z230,z4,z5,z164,z6]),(0,[z0,z2,z3,z4,z5,z380,z6]),(1,[z0,z49,z2,z46,z4,z6]),(0,[z0,z2,z3,z47,z4,z5,z6])],[(0,[z0,z381,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z382]),(0,[z0,z383,z2,z3,z4,z5,z6]),(0,[z0,z384,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z385,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z386,z6])],[(0,[z387,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z388,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z389]),(0,[z0,z390,z2,z3,z4,z5,z6])],[(0,[z263,z0,z2,z3,z91,z5,z6]),(0,[z0,z391,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z55])]],
   [[(0,[z87,z2,z3,z4,z12,z5,z6])],[(0,[z0,z2,z392,z3,z4,z5,z6]),(0,[z0,z2,z3,z138,z91,z5,z6]),(0,[z0,z393,z2,z3,z4,z5,z6]),(0,[z0,z394,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z163,z28]),(0,[z0,z2,z37,z3,z4,z155,z6]),(0,[z0,z2,z3,z47,z4,z83,z6]),(0,[z0,z395,z2,z3,z4,z5,z6])],[(0,[z0,z396,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z397])],[(0,[z0,z398,z2,z3,z4,z5,z6]),(0,[z399,z0,z2,z3,z4,z5,z6]),(0,[z0,z400,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z88,z6]),(0,[z0,z2,z3,z4,z5,z102,z81]),(0,[z0,z401,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z402,z5,z6]),(0,[z0,z49,z2,z46,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z403,z5,z6]),(0,[z0,z2,z3,z4,z5,z404,z6]),(0,[z0,z405,z2,z3,z4,z5,z6]),(0,[z0,z49,z11,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z406,z6]),(0,[z229,z0,z2,z3,z4,z12,z6]),(0,[z0,z2,z3,z4,z5,z407,z6]),(0,[z0,z2,z3,z4,z5,z6,z408]),(0,[z0,z2,z3,z4,z409,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z50])],[(0,[z0,z410,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z411,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z339]),(0,[z0,z2,z3,z4,z5,z6,z412])],[(0,[z0,z2,z3,z4,z5,z413,z6]),(0,[z0,z414,z2,z3,z4,z5,z6]),(0,[z0,z415,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z416,z6])],[(0,[z0,z2,z3,z25,z5,z121,z6]),(1,[z0,z2,z3,z4,z215,z5]),(0,[z0,z44,z2,z3,z47,z4,z6]),(0,[z244,z2,z3,z4,z5,z121,z6]),(0,[z0,z417,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z418]),(0,[z0,z2,z3,z4,z5,z6,z419])],[(0,[z0,z2,z3,z4,z5,z420,z6]),(0,[z0,z29,z2,z3,z4,z5,z6]),(0,[z421,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z37,z138,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z422])],[(0,[z0,z2,z3,z4,z5,z423,z6]),(0,[z0,z2,z3,z424,z4,z5,z6]),(0,[z0,z2,z3,z425,z4,z5,z6]),(0,[z0,z2,z3,z4,z426,z5,z6])],[(0,[z80,z0,z2,z3,z4,z5,z6]),(0,[z80,z0,z2,z3,z4,z5,z163]),(0,[z0,z18,z2,z127,z4,z5,z6]),(0,[z0,z2,z3,z138,z4,z427,z6]),(0,[z0,z428,z2,z3,z4,z5,z6])],[(0,[z429,z0,z2,z3,z4,z5,z6]),(0,[z0,z119,z3,z127,z4,z5,z6]),(0,[z430,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z127,z4,z5,z6]),(0,[z0,z52,z2,z3,z4,z5,z6]),(0,[z0,z2,z82,z3,z4,z31,z6]),(0,[z0,z2,z3,z4,z431,z5,z6]),(0,[z0,z2,z30,z3,z47,z4,z6])],[(0,[z0,z2,z3,z432,z4,z5,z6]),(0,[z433,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z434,z2,z3,z4,z5,z6]),(0,[z0,z49,z29,z2,z3,z4,z6]),(0,[z0,z2,z435,z3,z4,z5,z6])],[(0,[z436,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z437,z6]),(0,[z438,z0,z2,z3,z4,z5,z6]),(0,[z0,z439,z2,z3,z4,z5,z6]),(0,[z440,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z441,z4,z5,z6]),(0,[z0,z442,z2,z3,z4,z5,z6]),(0,[z0,z2,z443,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z444,z6]),(0,[z0,z2,z3,z445,z4,z5,z6]),(0,[z0,z2,z3,z4,z446,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z28]),(1,[z0,z2,z3,z4,z447,z6])],[(0,[z0,z2,z3,z4,z5,z448,z6]),(0,[z0,z2,z449,z3,z4,z5,z6]),(0,[z0,z450,z2,z3,z4,z5,z6]),(0,[z35,z368,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z451,z6]),(0,[z0,z18,z2,z3,z4,z5,z6]),(0,[z0,z29,z2,z3,z4,z21,z6])],[(0,[z174,z2,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z452,z4,z5,z6]),(0,[z0,z453,z2,z3,z4,z5,z6]),(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z455,z0,z2,z3,z4,z5,z6]),(0,[z0,z49,z2,z3,z305,z5,z6]),(0,[z0,z2,z3,z4,z5,z173,z6]),(0,[z0,z2,z456,z3,z4,z5,z6])],[(0,[z110,z0,z2,z79,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z457,z6]),(0,[z0,z170,z3,z4,z5,z164,z6]),(0,[z0,z2,z458,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z459])],[(0,[z0,z2,z3,z4,z149,z5,z6]),(0,[z0,z2,z460,z3,z4,z5,z6]),(0,[z0,z9,z2,z3,z172,z5,z6])]],
   [[(0,[z0,z2,z461,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z462,z6]),(0,[z0,z463,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z55])],[(0,[z0,z2,z3,z464,z4,z5,z6]),(0,[z263,z0,z2,z3,z4,z34,z6]),(0,[z0,z2,z3,z465,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z466]),(0,[z0,z2,z3,z4,z5,z467,z6]),(0,[z0,z2,z3,z468,z4,z5,z6]),(0,[z0,z469,z2,z3,z4,z5,z6])],[(0,[z110,z2,z3,z91,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z470,z6]),(0,[z263,z0,z2,z3,z4,z167,z6]),(0,[z0,z471,z2,z3,z4,z5,z6]),(0,[z87,z229,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z472,z4,z5,z6]),(0,[z0,z44,z2,z3,z4,z50,z6])],[(0,[z0,z2,z3,z4,z5,z473,z6]),(0,[z0,z2,z3,z474,z4,z5,z6]),(0,[z0,z475,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z476,z6])],[(0,[z0,z2,z477,z3,z4,z5,z6]),(0,[z0,z478,z2,z3,z4,z5,z6])],[(0,[z110,z0,z479,z3,z4,z5,z6]),(0,[z0,z2,z480,z3,z4,z5,z6]),(0,[z481,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z482,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z483]),(0,[z0,z2,z267,z3,z127,z4,z6]),(1,[z0,z2,z181,z4,z5,z102])],[(0,[z0,z484,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z485,z5,z6]),(0,[z486,z0,z2,z3,z4,z5,z6]),(0,[z0,z44,z29,z3,z4,z5,z6]),(0,[z0,z487,z2,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z271,z6]),(0,[z488,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z489,z3,z4,z5,z6]),(0,[z0,z217,z2,z3,z4,z5,z6]),(0,[z0,z49,z2,z3,z4,z31,z6]),(0,[z0,z15,z2,z3,z46,z4,z6]),(0,[z0,z2,z3,z490,z4,z5,z6])],[(0,[z0,z2,z3,z46,z4,z88,z6]),(0,[z368,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z491,z6])],[(0,[z492,z0,z2,z3,z4,z5,z6]),(0,[z263,z2,z3,z4,z25,z5,z6]),(0,[z0,z493,z2,z3,z4,z5,z6]),(0,[z0,z2,z494,z3,z4,z5,z6]),(0,[z0,z44,z2,z3,z4,z12,z6]),(0,[z0,z253,z2,z3,z4,z131,z5]),(0,[z35,z0,z170,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z427,z6]),(0,[z0,z2,z3,z4,z5,z495,z6])],[(0,[z0,z496,z2,z3,z4,z5,z6]),(0,[z497,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z498,z6])],[(0,[z110,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z499]),(0,[z0,z217,z2,z3,z5,z121,z6])],[(0,[z174,z0,z2,z3,z4,z5,z6]),(0,[z174,z105,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z500]),(0,[z501,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z502,z6])],[(0,[z0,z2,z3,z4,z5,z503,z6]),(0,[z0,z2,z30,z3,z4,z12,z6]),(0,[z0,z2,z3,z275,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z124]),(0,[z0,z2,z3,z4,z5,z6,z504])],[(0,[z0,z2,z3,z4,z5,z505,z6]),(0,[z0,z2,z3,z506,z4,z5,z6]),(0,[z0,z507,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z508,z5,z6])]],
   [[(0,[z0,z9,z180,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z509,z6]),(0,[z0,z29,z2,z3,z47,z4,z6]),(0,[z0,z2,z3,z27,z4,z5,z6]),(0,[z0,z2,z3,z47,z4,z50,z6]),(0,[z0,z2,z3,z4,z5,z6,z418])],[(0,[z0,z2,z3,z317,z4,z5,z6]),(0,[z35,z0,z3,z4,z5,z6,z209]),(0,[z0,z2,z3,z4,z5,z31,z6])],[(0,[z105,z0,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z132,z6]),(0,[z0,z2,z3,z510,z4,z5,z6])],[(0,[z104,z0,z2,z3,z4,z132,z6]),(0,[z0,z2,z511,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z209]),(0,[z0,z512,z2,z3,z4,z5,z6]),(0,[z0,z15,z11,z2,z3,z4,z6])],[(0,[z0,z513,z2,z3,z4,z5,z6]),(0,[z0,z514,z2,z3,z4,z5,z6]),(0,[z0,z44,z49,z2,z3,z4,z6]),(0,[z0,z2,z3,z515,z4,z5,z6])],[(0,[z0,z180,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z516,z6])],[(0,[z0,z2,z3,z4,z216,z5,z6]),(0,[z0,z2,z3,z4,z5,z517,z6]),(0,[z0,z2,z518,z3,z4,z5,z6]),(0,[z0,z2,z181,z3,z4,z5,z102]),(0,[z519,z0,z2,z3,z4,z5,z6])],[(0,[z0,z520,z2,z3,z4,z5,z6]),(0,[z0,z521,z2,z3,z4,z5,z6]),(1,[z24,z2,z3,z91,z5,z6]),(0,[z87,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z522]),(0,[z0,z523,z2,z3,z4,z5,z6]),(0,[z0,z524,z2,z3,z4,z5,z6]),(0,[z525,z0,z2,z3,z4,z5,z6]),(0,[z0,z20,z3,z4,z5,z164,z6]),(0,[z0,z2,z3,z4,z5,z526,z6]),(0,[z0,z2,z527,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z34,z6]),(0,[z0,z2,z528,z3,z4,z5,z6])],[(0,[z174,z0,z86,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z167,z6]),(0,[z0,z44,z2,z3,z4,z61,z6]),(0,[z0,z2,z3,z4,z147,z5,z50])],[(0,[z0,z2,z3,z4,z5,z6,z529])],[(0,[z242,z0,z2,z317,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z530,z6]),(0,[z0,z2,z3,z4,z5,z102,z163]),(0,[z0,z109,z2,z181,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z146,z6])],[(0,[z110,z0,z2,z3,z531,z5,z6]),(0,[z0,z2,z532,z3,z4,z5,z6]),(0,[z0,z2,z533,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z534,z6]),(0,[z0,z2,z82,z4,z5,z83,z6]),(0,[z0,z535,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z536,z4,z5,z6]),(1,[z0,z139,z3,z4,z5,z6])],[(0,[z0,z2,z3,z537,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z538,z6]),(0,[z0,z539,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z540,z4,z5,z6]),(0,[z0,z9,z2,z3,z5,z6,z10])],[(1,[z0,z2,z3,z4,z106,z6]),(0,[z0,z2,z3,z4,z88,z31,z6]),(1,[z0,z2,z267,z3,z4,z6])],[(0,[z541,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z542,z2,z3,z4,z5,z6]),(0,[z80,z104,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z543]),(0,[z0,z29,z2,z3,z4,z50,z6]),(1,[z0,z217,z2,z5,z121,z6]),(0,[z0,z2,z30,z3,z5,z121,z6]),(0,[z0,z2,z544,z3,z4,z5,z6]),(0,[z0,z139,z2,z3,z4,z5,z6])],[(1,[z0,z109,z2,z4,z5,z28])],[(0,[z35,z0,z2,z3,z4,z5,z209]),(0,[z545,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z546,z5,z6])],[(0,[z110,z0,z2,z3,z4,z5,z62]),(0,[z0,z2,z3,z4,z5,z6,z163]),(0,[z104,z2,z3,z4,z5,z81,z6]),(0,[z547,z0,z2,z3,z4,z5,z6]),(0,[z0,z180,z3,z230,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z548,z6]),(0,[z0,z549,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z550,z5,z6]),(0,[z104,z0,z2,z3,z4,z203,z6]),(0,[z0,z2,z3,z4,z131,z5,z6])],[(0,[z104,z0,z2,z3,z4,z5,z81]),(0,[z0,z551,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z447,z6,z10])],[(1,[z0,z2,z3,z531,z5,z6]),(0,[z0,z2,z3,z552,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z553,z6]),(0,[z0,z2,z3,z4,z5,z554,z6]),(0,[z2,z3,z4,z5,z36,z121,z6]),(0,[z0,z2,z3,z4,z5,z6,z555]),(0,[z0,z2,z3,z4,z5,z6,z556]),(0,[z0,z557,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z418,z10]),(1,[z0,z2,z3,z4,z147,z50])],[(0,[z263,z0,z2,z3,z25,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z558]),(0,[z0,z29,z2,z3,z4,z12,z6]),(0,[z0,z19,z3,z127,z4,z5,z6]),(0,[z0,z2,z3,z4,z305,z5,z6])],[(0,[z0,z2,z3,z4,z5,z559,z6]),(0,[z0,z2,z3,z138,z25,z5,z6]),(0,[z0,z2,z560,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z561,z5,z6]),(0,[z0,z2,z562,z3,z4,z5,z6])],[(1,[z105,z119,z3,z4,z5,z6]),(0,[z0,z2,z3,z563,z4,z5,z6]),(0,[z2,z3,z4,z5,z81,z6,z163]),(0,[z0,z2,z3,z4,z564,z5,z6]),(0,[z0,z2,z3,z47,z5,z121,z6]),(0,[z0,z565,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z566,z4,z5,z6]),(0,[z0,z2,z3,z4,z147,z5,z55])],[(0,[z0,z2,z3,z567,z4,z5,z6]),(0,[z0,z568,z2,z3,z4,z5,z6]),(0,[z0,z2,z569,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z570,z5,z6])],[(0,[z571,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z479,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z308,z6]),(1,[z0,z2,z3,z4,z5,z62]),(0,[z0,z2,z572,z3,z4,z5,z6]),(0,[z0,z2,z3,z573,z4,z5,z6]),(0,[z0,z2,z373,z3,z127,z4,z6]),(1,[z0,z369,z2,z3,z5,z6]),(1,[z0,z2,z3,z66,z5,z6]),(0,[z574,z0,z2,z3,z4,z5,z6])],[(0,[z0,z575,z2,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z4,z31,z6])],[(1,[z110,z2,z317,z4,z5,z6]),(1,[z80,z2,z3,z4,z5,z163]),(0,[z0,z2,z576,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z577])]],
   [[(0,[z0,z2,z578,z3,z4,z5,z6])],[(0,[z263,z2,z79,z3,z4,z5,z6]),(0,[z2,z3,z91,z4,z25,z5,z6]),(0,[z579,z0,z2,z3,z4,z5,z6]),(0,[z0,z580,z2,z3,z4,z5,z6]),(0,[z0,z2,z130,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z581,z5,z6]),(0,[z35,z0,z2,z3,z4,z5,z164]),(0,[z0,z2,z582,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z583,z6]),(0,[z0,z2,z584,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z161,z6])],[(0,[z0,z585,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z586,z5,z6]),(0,[z587,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z588,z6]),(0,[z589,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z590,z6]),(0,[z24,z0,z2,z3,z91,z5,z6]),(0,[z0,z591,z2,z3,z4,z5,z6]),(0,[z0,z592,z2,z3,z4,z5,z6]),(0,[z0,z2,z593,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z594])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z119,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z595,z5,z6]),(0,[z0,z596,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z339,z209]),(0,[z0,z597,z2,z3,z4,z5,z6])],[(0,[z0,z2,z598,z3,z4,z5,z6]),(0,[z0,z2,z599,z3,z4,z5,z6])],[(0,[z600,z0,z2,z3,z4,z5,z6])],[(0,[z110,z263,z2,z3,z4,z5,z6]),(0,[z0,z601,z2,z3,z4,z5,z6]),(0,[z0,z29,z2,z3,z4,z61,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z602]),(0,[z0,z2,z3,z4,z5,z6,z603]),(0,[z0,z2,z3,z4,z5,z447,z6])],[(0,[z0,z2,z3,z604,z4,z5,z6]),(0,[z0,z369,z2,z3,z5,z6,z209]),(0,[z0,z2,z82,z3,z4,z5,z6]),(0,[z0,z605,z2,z3,z4,z5,z6]),(0,[z0,z2,z606,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z607,z5,z6]),(0,[z608,z0,z2,z3,z4,z5,z6]),(0,[z0,z20,z2,z3,z5,z173,z6])],[(0,[z609,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z164,z6,z209]),(0,[z0,z2,z181,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z610,z5,z6])],[(0,[z0,z2,z3,z4,z215,z5,z6]),(0,[z0,z2,z3,z4,z5,z611,z6]),(0,[z0,z612,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z5,z6]),(0,[z0,z613,z2,z3,z4,z5,z6])],[(0,[z614,z0,z2,z3,z4,z5,z6]),(0,[z0,z615,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z616,z6]),(0,[z0,z2,z3,z617,z4,z5,z6]),(0,[z0,z49,z2,z30,z3,z4,z6])],[(0,[z0,z2,z3,z618,z4,z5,z6]),(0,[z0,z2,z619,z3,z4,z5,z6]),(0,[z0,z2,z3,z620,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z621]),(0,[z0,z2,z3,z4,z5,z6,z622])]],
   [[(1,[z0,z2,z3,z4,z216,z6]),(0,[z35,z0,z3,z230,z4,z5,z6])],[],[(0,[z263,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z623,z3,z4,z5,z6]),(0,[z0,z2,z3,z230,z4,z5,z6]),(0,[z0,z2,z3,z624,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z625,z6]),(0,[z0,z2,z3,z4,z626,z5,z6]),(0,[z627,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z138,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z628,z6])],[(1,[z0,z2,z373,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z629,z6]),(0,[z0,z2,z630,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z161,z5,z6])],[(0,[z0,z2,z3,z4,z5,z631,z6]),(0,[z0,z2,z3,z4,z5,z271,z6]),(0,[z0,z2,z3,z4,z5,z88,z6]),(0,[z0,z2,z3,z4,z5,z632,z6]),(0,[z0,z2,z3,z4,z5,z633,z6]),(0,[z0,z2,z3,z4,z5,z6,z634]),(0,[z0,z2,z3,z4,z5,z635,z6])],[(0,[z0,z170,z2,z3,z4,z5,z209])]],
   [[(0,[z0,z2,z3,z4,z5,z427,z6])],[(0,[z0,z109,z2,z3,z4,z5,z6])],[(0,[z636,z0,z2,z3,z4,z5,z6])],[(0,[z0,z18,z86,z3,z4,z5,z6]),(0,[z0,z49,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z637,z4,z5,z6]),(0,[z87,z0,z2,z3,z4,z12,z6]),(1,[z0,z20,z3,z131,z5,z6]),(0,[z0,z638,z2,z3,z4,z5,z6])],[(0,[z639,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z640,z5,z6]),(0,[z0,z2,z3,z4,z5,z641,z6]),(0,[z642,z0,z2,z3,z4,z5,z6]),(0,[z0,z643,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z644,z5,z6])],[(0,[z0,z2,z3,z531,z4,z5,z6]),(0,[z0,z2,z3,z4,z12,z50,z6]),(0,[z0,z2,z645,z3,z4,z5,z6]),(0,[z0,z9,z170,z2,z3,z4,z5]),(0,[z0,z2,z37,z3,z138,z5,z6]),(0,[z0,z2,z3,z138,z47,z5,z6]),(0,[z0,z646,z2,z3,z4,z5,z6])],[(0,[z2,z79,z3,z91,z4,z5,z6]),(0,[z0,z20,z2,z3,z230,z5,z6]),(0,[z0,z2,z3,z4,z5,z647,z6]),(0,[z648,z0,z2,z3,z4,z5,z6]),(0,[z0,z649,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z44,z2,z82,z3,z4,z6]),(0,[z0,z2,z650,z3,z4,z5,z6]),(0,[z0,z15,z2,z30,z3,z5,z6]),(0,[z0,z2,z3,z172,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z651,z6]),(0,[z0,z2,z3,z4,z652,z5,z6]),(0,[z0,z2,z3,z4,z653,z5,z6]),(1,[z0,z29,z3,z4,z21,z6]),(0,[z0,z2,z3,z4,z654,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z655])],[(1,[z0,z479,z3,z4,z5,z6]),(0,[z656,z0,z2,z3,z4,z5,z6])],[(0,[z657,z0,z2,z3,z4,z5,z6]),(0,[z105,z2,z3,z4,z5,z6,z163]),(0,[z658,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z46,z4,z5,z83,z6])],[(0,[z659,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z660]),(0,[z0,z2,z30,z82,z3,z4,z6])],[(0,[z0,z661,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z662,z6]),(0,[z35,z0,z9,z2,z3,z4,z5])],[(0,[z0,z170,z2,z3,z4,z5,z164]),(0,[z0,z2,z93,z3,z138,z4,z6]),(0,[z0,z2,z3,z4,z5,z663,z6])],[(0,[z0,z664,z2,z3,z4,z5,z6]),(0,[z0,z360,z2,z3,z4,z6,z209]),(0,[z0,z2,z3,z4,z5,z665,z6]),(0,[z0,z666,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z667,z4,z5,z6]),(1,[z0,z9,z2,z3,z5,z10])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z668,z5,z6])],[(0,[z0,z2,z669,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z670]),(0,[z0,z253,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z671,z6]),(0,[z0,z2,z3,z46,z4,z5,z6])],[(0,[z0,z2,z3,z4,z25,z5,z6]),(0,[z0,z2,z3,z4,z5,z672,z6]),(0,[z0,z2,z673,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z106,z6]),(0,[z0,z2,z674,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z675])],[],[(0,[z676,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z93,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z102,z6])],[(0,[z677,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z678,z5,z6]),(0,[z0,z2,z3,z4,z5,z679,z6]),(0,[z680,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z681,z6]),(0,[z0,z2,z3,z4,z5,z682,z6])],[(0,[z0,z2,z3,z4,z5,z6,z683]),(0,[z0,z20,z2,z3,z131,z5,z6]),(0,[z0,z2,z3,z684,z4,z5,z6]),(0,[z0,z2,z3,z5,z173,z6,z10])],[(0,[z0,z49,z2,z3,z66,z5,z6])],[(0,[z110,z0,z2,z317,z4,z5,z6]),(0,[z0,z685,z2,z3,z4,z5,z6]),(0,[z0,z15,z2,z30,z3,z4,z6])],[(0,[z0,z2,z3,z4,z12,z5,z6]),(0,[z686,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z687,z5,z6]),(0,[z0,z688,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z689,z3,z4,z5,z6]),(0,[z0,z2,z82,z3,z4,z50,z6]),(0,[z0,z690,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z691,z5,z6]),(0,[z0,z692,z2,z3,z4,z5,z6]),(0,[z0,z109,z2,z3,z4,z5,z102]),(0,[z0,z2,z3,z4,z147,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z693]),(0,[z229,z0,z2,z3,z4,z88,z6]),(0,[z0,z694,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z695])],[(1,[z263,z2,z3,z25,z5,z6])],[(0,[z0,z2,z3,z4,z12,z83,z6]),(0,[z0,z2,z3,z4,z5,z696,z6])],[(0,[z0,z2,z3,z4,z697,z5,z6]),(0,[z0,z698,z2,z3,z4,z5,z6])],[(0,[z699,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z700,z4,z5,z6]),(0,[z229,z2,z3,z4,z5,z88,z6])],[(0,[z0,z2,z3,z275,z4,z131,z6])],[(0,[z0,z2,z3,z701,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z702,z6]),(0,[z0,z29,z2,z82,z3,z4,z6]),(0,[z0,z2,z703,z3,z4,z5,z6])],[(0,[z0,z2,z3,z704,z4,z5,z6]),(0,[z0,z2,z3,z705,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z81,z28]),(0,[z0,z2,z706,z3,z4,z5,z6]),(0,[z0,z3,z230,z4,z131,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z272,z86,z3,z4,z5,z6]),(0,[z2,z3,z707,z4,z5,z6]),(0,[z0,z2,z3,z4,z708,z6]),(0,[z0,z2,z37,z138,z5,z6]),(0,[z0,z2,z3,z4,z5,z709])],[(0,[z547,z86,z3,z4,z5,z6]),(0,[z263,z2,z3,z149,z5,z6]),(0,[z0,z2,z3,z4,z5,z710]),(0,[z35,z0,z3,z4,z5,z259]),(0,[z0,z2,z711,z4,z83,z6])],[(0,[z0,z2,z3,z712,z5,z6]),(0,[z263,z2,z3,z713,z5,z6]),(0,[z0,z2,z3,z4,z5,z714]),(0,[z0,z2,z715,z4,z5,z6]),(0,[z0,z180,z3,z5,z6,z412])],[(0,[z0,z20,z3,z131,z5,z6]),(1,[z0,z20,z253,z3,z5])]],
   [[(0,[z242,z2,z79,z4,z5,z6]),(0,[z0,z2,z716,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z717])],[(0,[z0,z2,z3,z4,z718,z6]),(0,[z0,z2,z3,z149,z271,z6]),(0,[z2,z79,z707,z4,z5,z6]),(0,[z0,z719,z3,z4,z5,z6]),(0,[z35,z52,z3,z4,z5,z209])],[(0,[z205,z2,z3,z4,z5,z163]),(1,[z0,z720,z4,z5,z6]),(0,[z368,z2,z3,z4,z708,z6]),(0,[z0,z2,z721,z3,z4,z6]),(0,[z0,z722,z2,z3,z4,z6]),(0,[z0,z3,z4,z5,z6,z723]),(0,[z0,z2,z82,z375,z4,z6]),(0,[z0,z2,z3,z5,z173,z724])],[(0,[z0,z2,z725,z4,z5,z6]),(0,[z0,z2,z3,z4,z726,z6]),(0,[z0,z2,z3,z727,z4,z6]),(0,[z0,z44,z3,z4,z431,z6]),(0,[z0,z2,z3,z5,z6,z728]),(0,[z217,z2,z5,z36,z121,z6])]],
   [[(0,[z0,z20,z3,z215,z131,z5]),(0,[z0,z2,z3,z47,z427,z6]),(1,[z0,z2,z3,z4,z709])],[(0,[z0,z2,z3,z4,z729,z6]),(0,[z0,z730,z3,z4,z5,z6]),(0,[z0,z44,z3,z4,z289,z6]),(0,[z0,z29,z3,z4,z731,z6]),(0,[z0,z2,z3,z732,z5,z6]),(0,[z0,z733,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z734,z28])],[(0,[z0,z2,z3,z4,z5,z735]),(0,[z0,z2,z3,z4,z736,z6]),(0,[z0,z29,z3,z4,z640,z6]),(0,[z0,z2,z737,z4,z5,z6]),(0,[z0,z2,z3,z275,z4,z215]),(0,[z0,z2,z3,z4,z155,z6])],[(0,[z24,z2,z3,z91,z5,z6]),(0,[z738,z2,z3,z4,z5,z6]),(0,[z0,z2,z739,z4,z5,z6]),(1,[z0,z2,z740,z5,z6])]],
   [[(0,[z0,z2,z741,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z742]),(0,[z0,z2,z743,z3,z4,z6]),(0,[z0,z2,z744,z3,z4,z6]),(0,[z104,z2,z3,z4,z5,z631]),(0,[z0,z2,z3,z531,z271,z6]),(0,[z2,z79,z4,z5,z113,z6]),(0,[z0,z2,z3,z4,z34,z6]),(0,[z244,z2,z3,z25,z5,z6]),(0,[z0,z2,z3,z4,z5,z745]),(0,[z0,z20,z3,z7,z5,z6]),(0,[z0,z2,z3,z740,z5,z6]),(0,[z0,z478,z2,z5,z121,z6])],[(0,[z0,z18,z392,z4,z5,z6]),(0,[z0,z2,z3,z4,z746,z6]),(0,[z0,z664,z2,z4,z5,z28]),(0,[z0,z2,z3,z4,z747,z6]),(0,[z0,z20,z130,z3,z131,z6]),(0,[z0,z2,z3,z4,z5,z748]),(0,[z0,z2,z3,z4,z749,z6])],[(0,[z0,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z750]),(0,[z2,z751,z3,z4,z5,z6]),(0,[z752,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z753,z209]),(0,[z0,z49,z2,z46,z66,z6]),(0,[z0,z2,z181,z4,z5,z734]),(0,[z0,z2,z3,z172,z5,z173])],[(0,[z0,z111,z3,z4,z5,z120]),(0,[z244,z2,z3,z91,z5,z6]),(0,[z0,z51,z720,z4,z5,z6]),(0,[z754,z2,z3,z4,z5,z6]),(0,[z0,z253,z2,z130,z3,z4]),(0,[z0,z2,z30,z3,z617,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z755]),(0,[z0,z2,z756,z3,z4,z6]),(0,[z0,z139,z3,z4,z5,z6]),(0,[z0,z253,z180,z2,z3,z5])],[(0,[z0,z757,z3,z4,z5,z6]),(0,[z0,z2,z758,z3,z4,z6]),(0,[z0,z759,z2,z3,z4,z5]),(0,[z0,z2,z3,z760,z5,z6]),(0,[z0,z2,z3,z172,z5,z724])],[(0,[z0,z2,z3,z4,z106,z6]),(0,[z0,z2,z3,z761,z4,z6]),(0,[z0,z2,z3,z4,z762,z6]),(0,[z0,z763,z2,z3,z4,z6]),(0,[z0,z51,z373,z127,z4,z6]),(0,[z0,z2,z3,z4,z50,z459]),(0,[z0,z139,z9,z2,z3,z5])],[(0,[z0,z2,z3,z4,z271,z62]),(0,[z0,z764,z2,z3,z5,z6]),(0,[z0,z2,z3,z765,z5,z6]),(0,[z766,z2,z3,z4,z5,z6]),(0,[z0,z2,z130,z3,z4,z215]),(0,[z0,z2,z3,z4,z767,z6]),(0,[z0,z360,z2,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z4,z768,z6]),(0,[z0,z2,z3,z4,z769,z6]),(0,[z0,z2,z770,z4,z5,z6]),(0,[z0,z2,z3,z4,z771,z6]),(0,[z0,z217,z2,z5,z121,z6]),(0,[z0,z2,z3,z47,z31,z6])],[(0,[z110,z2,z707,z4,z5,z6]),(0,[z0,z2,z3,z4,z697,z50]),(0,[z0,z523,z2,z46,z4,z6]),(0,[z0,z180,z3,z772,z5,z6]),(0,[z0,z2,z3,z66,z427,z6]),(0,[z0,z109,z2,z4,z5,z28]),(0,[z0,z139,z9,z3,z5,z6])],[(0,[z368,z2,z3,z4,z5,z6]),(0,[z0,z2,z707,z4,z5,z6]),(0,[z0,z2,z3,z4,z773,z6]),(0,[z0,z774,z2,z3,z4,z6]),(0,[z0,z2,z3,z38,z4,z6]),(0,[z0,z2,z138,z740,z5,z6])],[(0,[z0,z775,z2,z3,z5,z6]),(0,[z0,z111,z3,z149,z5,z6]),(0,[z344,z2,z3,z91,z5,z6]),(0,[z2,z3,z4,z776,z88,z6]),(0,[z440,z2,z3,z4,z12,z6]),(0,[z0,z2,z3,z4,z5,z777]),(0,[z0,z2,z3,z772,z5,z6]),(0,[z0,z11,z2,z3,z4,z504]),(0,[z0,z139,z3,z5,z173,z6])]],
   [[(0,[z0,z2,z778,z3,z4,z6]),(0,[z0,z2,z3,z4,z779,z6]),(0,[z0,z2,z780,z3,z4,z6]),(0,[z0,z2,z3,z781,z5,z6]),(0,[z0,z369,z2,z3,z6,z124]),(0,[z0,z2,z3,z4,z782,z6]),(0,[z0,z783,z2,z3,z4,z6]),(0,[z0,z139,z9,z3,z5,z10])],[(0,[z35,z0,z3,z4,z5,z209]),(0,[z0,z2,z3,z4,z784,z6]),(0,[z0,z2,z3,z4,z785,z6])],[(0,[z0,z479,z3,z4,z308,z6]),(0,[z0,z2,z3,z4,z5,z786]),(0,[z0,z787,z3,z4,z5,z6]),(0,[z0,z2,z3,z788,z5,z6]),(0,[z0,z2,z789,z3,z4,z6]),(0,[z0,z2,z3,z790,z4,z6]),(0,[z0,z3,z4,z5,z164,z753]),(0,[z0,z2,z3,z4,z147,z50])],[(0,[z0,z791,z3,z4,z5,z6]),(0,[z0,z792,z3,z4,z5,z6]),(0,[z0,z15,z2,z3,z367,z6]),(0,[z0,z2,z3,z46,z66,z6]),(0,[z0,z9,z3,z5,z418,z10])]],
   [[(0,[z0,z2,z3,z793,z5,z6]),(0,[z0,z2,z3,z4,z794,z6]),(0,[z110,z479,z317,z4,z5,z6]),(0,[z263,z2,z3,z25,z34,z6]),(0,[z0,z2,z3,z4,z795,z6])],[(0,[z174,z86,z3,z4,z5,z6]),(0,[z105,z227,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z796,z6]),(0,[z0,z2,z3,z4,z797,z6]),(0,[z0,z2,z584,z4,z83,z6])],[(0,[z798,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z799,z6]),(0,[z0,z170,z3,z4,z5,z164]),(0,[z0,z369,z3,z5,z164,z6]),(0,[z0,z2,z3,z172,z564,z5]),(0,[z0,z2,z3,z4,z800,z6])],[(0,[z0,z2,z3,z4,z5,z801]),(0,[z0,z3,z4,z5,z164,z660]),(0,[z0,z2,z3,z4,z802,z5]),(0,[z0,z2,z46,z711,z4,z6])]],
   [[(0,[z2,z3,z713,z25,z5,z6]),(0,[z0,z2,z3,z4,z803,z6]),(0,[z0,z2,z804,z3,z4,z6]),(0,[z0,z15,z2,z3,z6,z419])],[(0,[z0,z2,z3,z4,z308,z6]),(0,[z0,z2,z3,z4,z5,z805]),(0,[z0,z2,z3,z806,z5,z6]),(0,[z0,z369,z2,z3,z5,z6]),(0,[z0,z2,z3,z66,z5,z6]),(0,[z2,z3,z4,z5,z807,z6])],[(0,[z0,z2,z3,z4,z308,z120]),(0,[z0,z808,z3,z4,z5,z6]),(0,[z0,z253,z3,z230,z4,z5]),(0,[z0,z2,z3,z4,z809,z6]),(0,[z0,z44,z3,z4,z61,z6]),(0,[z35,z0,z369,z3,z5,z209]),(0,[z0,z2,z3,z4,z810,z6]),(0,[z0,z11,z2,z3,z4,z709])],[(0,[z0,z2,z3,z4,z811,z6]),(0,[z110,z2,z317,z4,z5,z6]),(0,[z0,z11,z2,z3,z4,z529]),(0,[z0,z2,z4,z5,z102,z734])]],
   [[(0,[z110,z2,z317,z4,z5,z120]),(0,[z0,z2,z812,z4,z5,z6]),(0,[z0,z2,z3,z4,z813,z6]),(0,[z0,z2,z814,z3,z4,z6]),(1,[z0,z3,z772,z5,z6]),(0,[z0,z9,z2,z3,z161,z10])],[(0,[z0,z2,z3,z815,z5,z6]),(0,[z0,z2,z3,z5,z6,z816]),(0,[z0,z2,z3,z4,z5,z817]),(0,[z0,z2,z818,z3,z4,z6]),(0,[z0,z2,z819,z4,z5,z6]),(0,[z0,z2,z3,z4,z161,z6])],[(0,[z105,z119,z3,z4,z106,z6]),(0,[z0,z720,z127,z4,z5,z6]),(0,[z0,z18,z720,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z820])],[(0,[z0,z2,z3,z4,z5,z821]),(0,[z0,z2,z3,z4,z822,z6]),(0,[z0,z2,z3,z4,z5,z823]),(0,[z244,z2,z3,z4,z5,z6]),(0,[z486,z2,z3,z4,z12,z6]),(1,[z0,z3,z4,z731,z6])]],
   [[(0,[z0,z2,z494,z138,z5,z6]),(0,[z35,z0,z673,z3,z4,z5]),(0,[z0,z15,z2,z331,z3,z6]),(0,[z0,z3,z4,z447,z6,z418])],[(0,[z0,z2,z3,z4,z824,z6]),(0,[z0,z2,z3,z4,z5,z825]),(0,[z0,z3,z4,z5,z6,z418]),(0,[z0,z3,z4,z5,z826,z6])],[(0,[z0,z2,z3,z149,z308,z6]),(0,[z0,z827,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z828]),(0,[z0,z2,z37,z138,z38,z6])],[(0,[z2,z3,z4,z776,z5,z6]),(0,[z0,z2,z3,z4,z5,z829]),(0,[z0,z253,z2,z3,z4,z5]),(0,[z0,z44,z3,z4,z731,z6]),(0,[z0,z830,z2,z3,z5,z6]),(0,[z0,z831,z3,z4,z5,z6]),(0,[z0,z2,z598,z46,z4,z6])]],
   [[(0,[z2,z3,z4,z5,z36,z6]),(0,[z0,z20,z253,z3,z131,z5])],[(0,[z0,z2,z3,z4,z6,z832]),(0,[z0,z18,z19,z4,z5,z6]),(0,[z833,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z834,z6]),(0,[z0,z20,z673,z3,z5,z6]),(0,[z0,z9,z401,z2,z3,z5]),(0,[z835,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z836,z4,z6]),(0,[z0,z2,z3,z4,z837,z6]),(0,[z0,z2,z3,z4,z50,z709])],[(0,[z0,z2,z3,z838,z5,z6]),(0,[z0,z2,z839,z4,z5,z6]),(0,[z0,z2,z449,z4,z5,z102]),(0,[z0,z2,z3,z4,z840,z6])],[(0,[z0,z2,z3,z841,z5,z6]),(0,[z0,z842,z2,z3,z4,z5]),(0,[z0,z2,z4,z5,z6,z843]),(0,[z0,z2,z3,z844,z5,z6]),(0,[z0,z2,z3,z845,z5,z6]),(0,[z0,z2,z846,z4,z5,z6]),(0,[z0,z2,z3,z4,z847,z6]),(0,[z0,z15,z2,z848,z3,z6])]],
   [[(0,[z52,z2,z3,z4,z5,z6]),(0,[z244,z2,z3,z149,z5,z6]),(0,[z80,z2,z3,z4,z5,z777]),(0,[z849,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z275,z4,z6])],[(0,[z0,z2,z3,z531,z308,z6]),(0,[z0,z850,z3,z4,z5,z6]),(0,[z0,z601,z2,z5,z121,z6]),(0,[z298,z2,z3,z4,z5,z163]),(0,[z0,z44,z703,z3,z4,z6]),(0,[z244,z217,z2,z5,z121,z6]),(0,[z0,z231,z2,z30,z3,z6]),(0,[z0,z2,z37,z138,z427,z6]),(1,[z0,z139,z9,z3,z5]),(0,[z0,z139,z3,z4,z447,z6])],[(0,[z0,z2,z4,z851,z5,z6]),(0,[z352,z2,z3,z4,z5,z81]),(0,[z0,z2,z3,z852,z5,z6]),(0,[z0,z2,z853,z3,z4,z6])],[(0,[z110,z2,z317,z531,z5,z6]),(0,[z0,z109,z2,z4,z5,z734])]],
   [[(0,[z0,z2,z3,z4,z216,z6]),(0,[z0,z2,z3,z854,z5,z6]),(0,[z0,z2,z3,z855,z5,z6]),(0,[z0,z2,z3,z856,z4,z6]),(0,[z35,z0,z3,z4,z124,z209]),(0,[z0,z2,z3,z424,z47,z6]),(0,[z0,z3,z857,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z858]),(0,[z0,z49,z2,z711,z4,z6]),(0,[z0,z2,z3,z5,z724,z10])],[(0,[z0,z2,z3,z4,z859,z6]),(0,[z0,z2,z82,z701,z4,z6]),(0,[z0,z2,z3,z47,z276,z6]),(0,[z0,z2,z3,z4,z5,z753]),(0,[z0,z2,z598,z138,z5,z6])],[(0,[z0,z860,z2,z4,z5,z6]),(0,[z0,z2,z3,z861,z5,z6])]],
   [[(0,[z0,z862,z2,z3,z4,z5]),(0,[z0,z2,z3,z863,z5,z6]),(0,[z60,z119,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z308,z62]),(0,[z0,z2,z3,z864,z5,z6]),(0,[z0,z2,z3,z4,z865,z6]),(0,[z866,z2,z3,z4,z5,z6])],[(1,[z751,z3,z4,z5,z6]),(0,[z0,z867,z3,z4,z5,z6]),(0,[z0,z868,z2,z3,z4,z6]),(0,[z0,z2,z130,z3,z4,z6]),(0,[z0,z253,z2,z3,z275,z4]),(0,[z0,z2,z3,z4,z869,z6]),(0,[z0,z870,z2,z3,z4,z6]),(0,[z0,z15,z2,z30,z3,z6]),(0,[z0,z2,z848,z3,z31,z6])],[(0,[z110,z2,z317,z4,z5,z62]),(0,[z0,z2,z3,z4,z871,z6]),(0,[z0,z3,z4,z5,z731,z6]),(0,[z368,z2,z3,z4,z872,z6]),(0,[z0,z49,z2,z4,z6,z135])],[(0,[z0,z2,z3,z4,z873,z6]),(0,[z0,z2,z3,z4,z5,z874]),(0,[z2,z3,z713,z4,z5,z6]),(1,[z0,z2,z711,z4,z6]),(0,[z0,z2,z3,z875,z5,z6]),(1,[z0,z2,z4,z5,z734])]],
   [[(0,[z751,z86,z3,z4,z5,z6]),(0,[z0,z876,z3,z4,z5,z6]),(0,[z0,z2,z877,z4,z5,z6]),(0,[z0,z20,z253,z2,z3,z5]),(0,[z0,z2,z37,z93,z138,z6])],[(0,[z0,z878,z2,z3,z5,z6]),(0,[z104,z2,z3,z4,z132,z81]),(0,[z0,z2,z37,z138,z155,z6])],[(0,[z0,z879,z3,z4,z5,z6]),(0,[z35,z0,z3,z5,z339,z209]),(0,[z0,z2,z3,z47,z546,z6]),(0,[z0,z9,z2,z3,z5,z724])],[(0,[z2,z3,z4,z12,z776,z6]),(0,[z0,z2,z848,z3,z5,z6]),(0,[z0,z880,z3,z4,z5,z6]),(0,[z0,z881,z2,z3,z4,z6])]],
   [[(0,[z2,z3,z91,z5,z420,z6]),(0,[z0,z2,z3,z4,z882,z6]),(0,[z0,z2,z740,z5,z121,z6])],[(0,[z0,z2,z3,z4,z883,z6]),(0,[z2,z3,z4,z5,z777,z163]),(0,[z0,z20,z3,z275,z131,z6]),(0,[z0,z109,z2,z27,z4,z28])],[(0,[z104,z2,z3,z4,z5,z81]),(0,[z0,z3,z720,z4,z5,z6]),(0,[z0,z2,z3,z884,z5,z6]),(0,[z0,z885,z2,z3,z4,z6]),(0,[z886,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z724])],[(0,[z0,z887,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z753]),(0,[z244,z2,z3,z4,z888,z6]),(0,[z0,z139,z3,z172,z4,z5])]],
   [[(0,[z0,z2,z889,z4,z5,z6]),(0,[z0,z2,z3,z890,z4,z6]),(0,[z891,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z124])],[(0,[z0,z2,z3,z4,z892,z6]),(0,[z893,z2,z3,z4,z5,z6]),(0,[z0,z29,z3,z4,z21,z6]),(0,[z0,z2,z82,z4,z83,z6])],[(0,[z0,z479,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z894,z6]),(0,[z0,z2,z3,z4,z895,z6]),(0,[z0,z2,z3,z4,z896,z6]),(0,[z0,z369,z170,z2,z3,z5])],[(0,[z0,z479,z3,z4,z5,z120]),(0,[z0,z2,z3,z897,z4,z6]),(0,[z87,z2,z3,z4,z776,z6]),(0,[z0,z898,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z339])]],
   [[(0,[z105,z119,z3,z4,z216,z6]),(0,[z0,z2,z3,z899,z5,z6]),(0,[z0,z2,z900,z3,z4,z6]),(0,[z0,z2,z3,z4,z132,z6]),(0,[z0,z2,z4,z740,z5,z6])],[(0,[z0,z2,z901,z3,z4,z6]),(0,[z0,z2,z3,z902,z5,z6]),(0,[z0,z170,z3,z4,z644,z5])],[(0,[z0,z2,z3,z903,z5,z6]),(0,[z0,z2,z3,z4,z904,z6]),(0,[z0,z2,z3,z4,z905,z6])],[(0,[z0,z906,z2,z3,z5,z6]),(0,[z0,z2,z3,z907,z4,z6]),(0,[z0,z170,z3,z4,z5,z753]),(0,[z908,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z909,z4,z6]),(0,[z0,z910,z2,z3,z4,z5]),(0,[z0,z911,z2,z3,z4,z6]),(0,[z2,z3,z91,z149,z5,z6]),(0,[z0,z2,z3,z912,z5,z6]),(0,[z0,z2,z3,z4,z913,z6]),(0,[z0,z3,z914,z4,z5,z6]),(0,[z0,z9,z2,z3,z5,z10])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z91,z713,z5,z6]),(0,[z0,z2,z3,z193,z31,z6]),(0,[z0,z44,z2,z3,z66,z6]),(0,[z0,z2,z915,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z120]),(0,[z104,z2,z3,z4,z203,z81]),(0,[z0,z2,z3,z66,z50,z6])],[(0,[z0,z479,z3,z149,z5,z6]),(0,[z0,z916,z2,z4,z5,z6]),(0,[z589,z2,z3,z4,z88,z6]),(0,[z0,z2,z3,z917,z5,z6]),(0,[z0,z2,z3,z4,z918,z6]),(0,[z0,z217,z2,z740,z5,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z709])]],
   [[(0,[z0,z920,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z167,z6]),(0,[z0,z2,z3,z4,z921,z6]),(0,[z0,z2,z922,z3,z4,z6]),(0,[z923,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z709,z55])],[(0,[z119,z751,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z924,z6]),(0,[z0,z2,z3,z47,z134,z6]),(0,[z0,z2,z3,z4,z146,z6])],[(0,[z0,z2,z3,z4,z925,z6]),(0,[z110,z2,z317,z4,z271,z6]),(0,[z35,z0,z3,z128,z4,z5]),(0,[z0,z2,z848,z3,z4,z6])],[(0,[z194,z2,z3,z4,z12,z6]),(0,[z0,z2,z30,z848,z3,z6])]],
   [[(0,[z0,z2,z3,z4,z926,z6]),(0,[z110,z2,z288,z4,z5,z6]),(0,[z0,z2,z3,z4,z927,z6]),(0,[z0,z928,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z929,z6])],[(0,[z0,z228,z127,z4,z5,z6]),(0,[z0,z930,z3,z4,z5,z6]),(0,[z0,z2,z267,z3,z4,z6]),(0,[z931,z2,z3,z4,z5,z6]),(0,[z35,z0,z3,z4,z5,z753]),(0,[z0,z2,z3,z6,z124,z339])],[(0,[z0,z2,z3,z4,z932,z6]),(0,[z0,z2,z3,z149,z5,z6]),(0,[z0,z479,z3,z531,z5,z6]),(0,[z23,z2,z3,z4,z88,z6]),(0,[z600,z2,z3,z4,z88,z6]),(0,[z0,z2,z3,z933,z5,z6])],[(0,[z0,z2,z934,z4,z5,z6]),(0,[z0,z935,z2,z4,z5,z6]),(0,[z0,z2,z3,z149,z5,z120]),(0,[z0,z2,z3,z713,z5,z6]),(0,[z648,z2,z3,z4,z88,z6]),(0,[z0,z2,z3,z4,z731,z6]),(0,[z0,z49,z2,z46,z4,z6]),(0,[z0,z49,z2,z46,z305,z6]),(0,[z0,z3,z4,z161,z6,z418])]],
   [[(0,[z0,z3,z772,z131,z5,z6]),(0,[z936,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z21,z731,z6]),(0,[z0,z29,z107,z3,z4,z6]),(0,[z0,z2,z848,z3,z47,z6])],[(0,[z2,z707,z317,z4,z5,z6]),(0,[z0,z2,z3,z4,z203,z6]),(0,[z229,z2,z3,z4,z776,z6]),(0,[z0,z2,z3,z937,z5,z6]),(0,[z0,z3,z4,z772,z5,z6]),(0,[z35,z0,z369,z3,z4,z5]),(0,[z0,z360,z2,z3,z6,z339])],[(0,[z0,z2,z3,z4,z938,z6]),(0,[z0,z2,z3,z4,z939,z6]),(0,[z0,z2,z3,z940,z5,z6]),(0,[z0,z2,z3,z4,z941,z6]),(0,[z0,z2,z3,z4,z942,z6]),(0,[z0,z2,z3,z943,z4,z6]),(0,[z0,z2,z37,z740,z5,z6]),(0,[z0,z2,z3,z944,z4,z6]),(0,[z0,z2,z3,z4,z50,z634]),(0,[z0,z2,z945,z4,z5,z6])],[(0,[z0,z111,z3,z531,z5,z6]),(0,[z242,z2,z707,z4,z5,z6]),(0,[z87,z2,z3,z4,z12,z6]),(0,[z0,z946,z3,z4,z5,z6]),(0,[z0,z9,z2,z3,z7,z5]),(0,[z0,z2,z3,z4,z947,z6])]],
   [[(0,[z0,z2,z3,z5,z6,z948]),(0,[z0,z51,z127,z4,z5,z6]),(0,[z0,z20,z3,z772,z5,z6]),(0,[z0,z949,z2,z3,z4,z6]),(0,[z0,z2,z3,z138,z38,z6]),(0,[z0,z2,z950,z3,z4,z6]),(0,[z0,z109,z2,z4,z146,z28])],[(0,[z0,z2,z3,z531,z5,z6]),(0,[z0,z479,z3,z4,z5,z62]),(0,[z263,z2,z3,z25,z5,z6]),(0,[z0,z2,z3,z4,z951,z6]),(0,[z952,z2,z3,z4,z5,z6]),(0,[z35,z368,z3,z4,z5,z209]),(0,[z0,z2,z30,z3,z427,z6]),(0,[z0,z2,z3,z4,z953,z6])],[(0,[z0,z2,z3,z4,z6,z954]),(0,[z0,z2,z3,z4,z955,z6]),(0,[z0,z2,z3,z531,z5,z120]),(0,[z0,z9,z2,z3,z5,z259]),(0,[z35,z0,z20,z9,z3,z5]),(0,[z0,z2,z3,z66,z31,z6]),(0,[z0,z2,z3,z4,z147,z709])],[(0,[z0,z2,z3,z4,z956,z6]),(0,[z2,z3,z4,z5,z81,z777]),(0,[z2,z3,z4,z5,z6,z957])]],
   [[(0,[z0,z2,z3,z4,z5,z958]),(0,[z0,z2,z3,z4,z5,z959]),(0,[z263,z2,z3,z25,z167,z6]),(0,[z0,z2,z3,z5,z6,z960]),(0,[z0,z20,z253,z3,z4,z5]),(0,[z0,z2,z3,z4,z961,z6]),(0,[z0,z2,z3,z4,z962,z6])],[(0,[z105,z119,z3,z4,z5,z6]),(0,[z0,z2,z3,z963,z4,z5]),(0,[z0,z2,z3,z4,z964,z6]),(0,[z0,z2,z3,z4,z6,z965]),(0,[z0,z49,z2,z624,z4,z6]),(0,[z0,z966,z3,z4,z5,z6])],[(0,[z0,z111,z3,z4,z308,z6]),(0,[z0,z111,z3,z4,z5,z62]),(1,[z2,z707,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z967]),(0,[z0,z2,z3,z4,z968,z6]),(0,[z0,z3,z230,z772,z5,z6]),(0,[z0,z2,z3,z969,z4,z6])],[(0,[z0,z2,z4,z970,z5,z6]),(0,[z0,z2,z3,z4,z971,z6]),(1,[z2,z3,z4,z5,z777]),(0,[z0,z2,z3,z972,z5,z6]),(0,[z0,z11,z2,z3,z4,z354]),(0,[z0,z2,z3,z973,z5,z6]),(0,[z0,z11,z2,z3,z66,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z974]),(0,[z0,z2,z3,z4,z5,z62]),(0,[z110,z111,z317,z4,z5,z6]),(0,[z574,z2,z3,z4,z12,z6]),(0,[z0,z11,z2,z3,z4,z358]),(0,[z2,z3,z4,z5,z975,z6]),(0,[z0,z976,z3,z4,z5,z6]),(0,[z0,z49,z2,z424,z4,z6])],[(0,[z0,z2,z3,z4,z977,z6]),(0,[z0,z978,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z979,z6]),(0,[z0,z2,z3,z980,z4,z6]),(0,[z0,z2,z3,z4,z6,z981]),(0,[z0,z29,z3,z4,z6,z67]),(0,[z0,z2,z3,z4,z982,z6]),(0,[z0,z2,z3,z4,z983,z6])],[(0,[z0,z2,z3,z4,z984,z6]),(1,[z2,z3,z713,z5,z6]),(0,[z80,z2,z3,z4,z5,z163]),(0,[z0,z2,z3,z4,z215,z5]),(0,[z0,z2,z3,z38,z121,z6])],[(0,[z229,z2,z3,z4,z88,z6]),(0,[z0,z2,z3,z5,z6,z985]),(0,[z0,z180,z3,z230,z5,z6]),(0,[z0,z2,z3,z4,z5,z986]),(0,[z0,z987,z3,z4,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z6,z753]),(0,[z988,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z734]),(0,[z0,z139,z3,z4,z161,z6])],[(0,[z0,z2,z989,z4,z5,z6]),(0,[z0,z990,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z991]),(0,[z0,z2,z3,z4,z888,z6]),(1,[z0,z2,z848,z3,z6]),(0,[z0,z3,z4,z5,z6,z992])],[(0,[z2,z3,z4,z5,z6,z777]),(0,[z0,z993,z2,z3,z4,z5]),(0,[z0,z44,z3,z510,z4,z6]),(0,[z0,z2,z3,z66,z83,z6])],[(0,[z0,z2,z3,z4,z5,z994]),(0,[z0,z51,z267,z127,z4,z6]),(0,[z0,z20,z3,z5,z647,z6])]],
   [[(0,[z0,z2,z3,z4,z995,z5]),(0,[z0,z2,z3,z996,z4,z6]),(0,[z0,z2,z3,z5,z173,z70]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z47,z610,z6]),(0,[z0,z2,z3,z4,z998,z6])],[(0,[z0,z751,z3,z4,z5,z6]),(0,[z105,z751,z3,z4,z5,z6]),(0,[z0,z2,z3,z149,z5,z62]),(0,[z0,z999,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1000]),(0,[z0,z9,z2,z3,z447,z10])],[(0,[z174,z751,z3,z4,z5,z6]),(0,[z0,z1001,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z776,z6]),(0,[z0,z29,z2,z3,z66,z6]),(0,[z0,z2,z3,z4,z447,z6])],[(0,[z110,z2,z317,z149,z5,z6]),(0,[z0,z1002,z3,z4,z5,z6]),(0,[z0,z19,z720,z4,z5,z6]),(0,[z0,z3,z230,z5,z6,z318]),(0,[z0,z2,z3,z5,z6,z724])]],
   [[(0,[z0,z1003,z2,z3,z4,z6]),(0,[z24,z2,z3,z713,z5,z6]),(0,[z0,z2,z3,z4,z6,z1004]),(0,[z0,z2,z3,z4,z1005,z6]),(0,[z0,z2,z3,z4,z50,z675]),(0,[z0,z2,z3,z1006,z5,z6]),(0,[z0,z11,z2,z3,z4,z55])],[(0,[z0,z2,z3,z4,z1007,z6]),(0,[z0,z2,z3,z4,z6,z1008]),(0,[z0,z2,z3,z4,z872,z6]),(0,[z0,z2,z82,z711,z4,z6])],[(0,[z0,z2,z3,z4,z5,z1009]),(0,[z35,z0,z369,z2,z3,z5])],[(0,[z0,z2,z3,z4,z1010,z6]),(0,[z0,z2,z39,z4,z83,z6]),(0,[z0,z2,z3,z1011,z5,z6]),(0,[z0,z369,z360,z2,z3,z6])]],
   [[(0,[z0,z2,z3,z4,z1012,z6]),(0,[z0,z2,z3,z531,z5,z62]),(0,[z0,z2,z1013,z4,z5,z6]),(1,[z35,z0,z369,z3,z5]),(0,[z0,z2,z82,z225,z4,z6]),(1,[z0,z2,z3,z5,z724])],[(0,[z0,z479,z3,z4,z271,z6]),(0,[z0,z2,z3,z4,z1014,z6]),(0,[z0,z2,z3,z4,z1015,z6]),(0,[z0,z2,z3,z4,z1016,z6]),(0,[z0,z2,z3,z1017,z5,z6]),(0,[z35,z0,z369,z3,z5,z6]),(0,[z0,z2,z3,z4,z1018,z6])],[(0,[z0,z2,z3,z1019,z5,z6]),(0,[z0,z1020,z3,z4,z5,z6]),(0,[z0,z2,z3,z1021,z5,z6]),(0,[z0,z2,z4,z5,z6,z1022]),(0,[z0,z2,z3,z4,z1023,z6]),(0,[z0,z2,z30,z3,z66,z6])],[(0,[z110,z2,z317,z4,z308,z6]),(0,[z35,z0,z360,z3,z4,z209])]],
   [[(0,[z0,z2,z93,z3,z4,z6]),(0,[z244,z2,z3,z4,z800,z6])],[(0,[z0,z2,z720,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z1024]),(0,[z0,z1025,z3,z4,z5,z6]),(0,[z0,z2,z3,z27,z4,z6]),(0,[z0,z139,z9,z3,z4,z5])],[(0,[z0,z111,z3,z4,z271,z6]),(0,[z0,z2,z181,z4,z5,z102])],[(0,[z0,z2,z3,z4,z1026,z6]),(0,[z0,z2,z3,z1027,z5,z6]),(0,[z0,z3,z4,z5,z6,z1028]),(0,[z0,z2,z3,z4,z1029,z6]),(0,[z0,z2,z711,z4,z5,z6]),(0,[z0,z2,z1030,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z4,z271,z6]),(0,[z0,z2,z3,z4,z5,z1031]),(0,[z0,z394,z2,z30,z3,z6]),(0,[z0,z2,z373,z3,z4,z6]),(0,[z0,z20,z253,z3,z5,z6]),(0,[z0,z2,z3,z4,z1032,z6])],[(0,[z0,z2,z3,z4,z271,z120]),(0,[z0,z3,z4,z5,z6,z1033]),(1,[z2,z3,z4,z776,z6]),(0,[z0,z2,z1034,z3,z4,z6]),(0,[z0,z2,z3,z1035,z5,z6])],[(0,[z0,z1036,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z1037,z6]),(0,[z0,z2,z4,z5,z6,z1038]),(0,[z0,z2,z3,z4,z1039,z6]),(0,[z1040,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z427,z6]),(0,[z0,z2,z3,z1041,z5,z6]),(0,[z0,z2,z1042,z4,z5,z6])],[(0,[z104,z2,z3,z4,z5,z777]),(0,[z0,z1043,z2,z3,z4,z5]),(0,[z0,z3,z4,z731,z61,z6]),(0,[z0,z29,z460,z3,z4,z6]),(0,[z0,z2,z3,z305,z5,z6]),(0,[z0,z2,z3,z711,z4,z6]),(0,[z0,z2,z3,z4,z5,z734])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 557) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 557).take 461) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1018)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [557, 461] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 92).take 36).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [92, 36] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_41768

theorem PEqualNP.Outside.L_meta_41768 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677312 * 2 ^ 32 + 3941132800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677312 * 2 ^ 32 + 3941132800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41768.solve