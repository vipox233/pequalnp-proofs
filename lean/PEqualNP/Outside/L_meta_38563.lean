import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38563

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
  Nat.testBit (4276676840 * 2 ^ 32 + 4272482472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0030a28500ca14b0#64 ++ 0x80018514280650a5#64 ++ 0x8071e78f01fe3fff#64 ++ 0x7c038f3c780ff1ff#64 : BitVec 256),
   (0x018649328624ca45#64 ++ 0x000c324994312652#64 ++ 0xa38e79f38e27ce7e#64 ++ 0xdd1c73cf9c713e73#64 : BitVec 256),
   (0x0c0b1458b0316306#64 ++ 0x006058a2c5818b18#64 ++ 0xdc0f9e7cf039f39d#64 ++ 0xf6e07cf3e781cf9c#64 : BitVec 256),
   (0xb6d01f805b41bc18#64 ++ 0x05b680fc02da0de0#64 ++ 0xfff01f80ffc1fc1b#64 ++ 0xefff80fc07fe0fe0#64 : BitVec 256),
   (0x5b6fe000edbe0000#64 ++ 0x0adb7f00076df000#64 ++ 0x7fffe000fffe0017#64 ++ 0xebffff0007fff000#64 : BitVec 256),
   (0x7ffdffef00000000#64 ++ 0x13ffefff78000000#64 ++ 0x7fffffff0000000f#64 ++ 0xd3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00020010b0fb77b6 0x800010008587dbbd 0x80000000f1fffff0 0x2c000000078fffff

def z1 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071e78f01fe3fff 0x7c038f3c780ff1ff

def z2 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e79f38e27ce7e 0xdd1c73cf9c713e73

def z3 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9e7cf039f39d 0xf6e07cf3e781cf9c

def z4 : W := mkw 0x0c3bb6ddb0fb77b6 0x8061ddb6ed87dbbd 0xdc7ffffff1ffffff 0xfee3ffffff8fffff

def z5 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe000fffe0017 0xebffff0007fff000

def z6 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01f80ffc1fc1b 0xefff80fc07fe0fe0

def z7 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x00000000f001c000 0x0000000007800e00

def z8 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff0000000f 0xd3fffffff8000000

def z9 : W := mkw 0x0020a005008a00a0 0x8001050028045005 0x0001e00f003e03e4 0x10000f007801f01f

def z10 : W := mkw 0xb6c01d005b01a808 0x05b600e802d80d40 0x7f801800fe01c000 0x83fc00c007f00e00

def z11 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e79f30000000e 0xd11c73cf98000000

def z12 : W := mkw 0xb65016805b41bc18 0x05b280b402da0de0 0xdc700600ffc1fc11 0x2ee3803007fe0fe0

def z13 : W := mkw 0x490f4000a4340000 0x0a487a000521a000 0x000e000000000000 0x0000700000000000

def z14 : W := mkw 0x37d45fa200000000 0x01bea2fd10000000 0x7ffe7ff30000000f 0xd3fff3ff98000000

def z15 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071860c01d83181 0x20038c30600ec18c

def z16 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e18708e01c000 0x811c70c384700e00

def z17 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800000008e27ce70 0x0c00000004713e73

def z18 : W := mkw 0x800000005b41bc18 0x0400000002da0de0 0x80000000ffc1fc10 0x2c00000007fe0fe0

def z19 : W := mkw 0xa4801d001201a808 0x052400e800900d40 0x000018000001c000 0x000000c000000e00

def z20 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80001f800001fc08 0x040000fc00000fe0

def z21 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0xffffffff01fe3fff 0xfffffffff80ff1ff

def z22 : W := mkw 0x01964bb28664de55 0x000cb25d943326f2 0xa3fe7ff38fe7fe7f 0xfd1ff3ff9c7f3ff3

def z23 : W := mkw 0x0002000080200000 0x0000100004010000 0x000e000080200014 0xc000700004010000

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0x000e18700000000c 0xd00070c380000000

def z25 : W := mkw 0x0106403284244245 0x0008320194212212 0x000e607300260264 0x1000730398013013

def z26 : W := mkw 0x0400140010012000 0x002000a000800900 0xdc001e00f001f019 0xe6e000f007800f80

def z27 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0xffffffffffc1fc1f 0xfffffffffffe0fe0

def z28 : W := mkw 0x0020a000008a0000 0x0001050000045000 0x0071e00001fe0017 0x68038f00000ff000

def z29 : W := mkw 0x7fdd5fef00000000 0x13feeaff78000000 0x7f8e1fff00000008 0x93fc70fff8000000

def z30 : W := mkw 0x7feffd6aedbe0000 0x1bff7feb576df000 0x7ffff870fffe0017 0xebffffc387fff000

def z31 : W := mkw 0xb6d21f90db61fe1c 0x05b690fc86db0ff0 0xfffe1ff0ffe1fe1f 0xfffff0ff87ff0ff0

def z32 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0f867c70383385 0x32e07c33e381c19c

def z33 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x000fe07f00000004 0x10007f03f8000000

def z34 : W := mkw 0x7fffffefedbe0000 0x1bffffff7f6df000 0x7ffffffffffe001f 0xfbfffffffffff000

def z35 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0ffffff03fffff 0xfee07fffff81ffff

def z36 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001860c0038339d 0x74000c306001c19c

def z37 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff01980ffc1cc02 0x8bff80cc07fe0e60

def z38 : W := mkw 0x5a69a000699a0000 0x0ad34d00034cd000 0x5c71800071d80001 0x22e38c00038ec000

def z39 : W := mkw 0x00100285004014b0 0x80008014280200a5 0x0000060c00003180 0x000000306000018c

def z40 : W := mkw 0x5f6ff458fdbf6306 0x0afb7fa2c7edfb18 0xfffffe7cfffff39f 0xfffffff3e7ffff9c

def z41 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e187000000000 0x83fc70c380000000

def z42 : W := mkw 0x1240000049000000 0x0092000002480000 0x7ff00000ffc00013 0xebff800007fe0000

def z43 : W := mkw 0x0002001080204204 0x0000100084010210 0x800e18708021c21c 0xd40070c384010e10

def z44 : W := mkw 0x0080090002008800 0x0004004800100440 0xa38019808e01cc1a 0xcd1c00cc04700e60

def z45 : W := mkw 0x7ffdffef02008800 0x13ffefff78100440 0xffffffff8e01cc1f 0xdffffffffc700e60

def z46 : W := mkw 0xff7ff680fdff3418 0x0ffbffb407eff9a0 0x7fffe600fffe3017 0xebffff3007fff180

def z47 : W := mkw 0x0809004800000000 0x0040480240000000 0x000f807c00000004 0x10007c03e0000000

def z48 : W := mkw 0x080b0058a0304306 0x00405802c5018218 0x000f807c00380384 0x10007c03e001c01c

def z49 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0e1870f001c000 0x82e070c387800e00

def z50 : W := mkw 0x7fedfd6f00000000 0x13ff6feb78000000 0x7f8ff87f00000004 0x93fc7fc3f8000000

def z51 : W := mkw 0x0c09144830112102 0x006048a241808908 0x5c01860c70183181 0x22e00c306380c18c

def z52 : W := mkw 0x05865d329625ea45 0x002c32e994b12f52 0xff8e7ff3fe27fe7f 0xfffc73ff9ff13ff3

def z53 : W := mkw 0x24901fef00000000 0x112480ff78000000 0x00001fff00000008 0x100000fff8000000

def z54 : W := mkw 0x0000000000401410 0x00000000000200a0 0x8000000001c03c10 0x2c000000000e01e0

def z55 : W := mkw 0xb7c65d32df25ea4d 0x05be32e996f92f52 0xff8e79f3fe27ce7e 0xdffc73cf9ff13e73

def z56 : W := mkw 0x0106400084240000 0x0008320004212000 0x238e60008e260016 0xc91c730004713000

def z57 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f9e7c0000000d 0xd2e07cf3e0000000

def z58 : W := mkw 0x00020000edbe0000 0x08001000076df000 0x00000000fffe0010 0x2800000007fff000

def z59 : W := mkw 0x5b6de00000000000 0x02db6f0000000000 0x7fffe00000000007 0xc3ffff0000000000

def z60 : W := mkw 0x0d8f5d7ab635eb47 0x006c7aebd5b1af5a 0xff8ffffffe3fffff 0xfffc7ffffff1ffff

def z61 : W := mkw 0x098f4932a634ca45 0x004c7a499531a652 0xff8ff9f3fe3fce7f 0xfffc7fcf9ff1fe73

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0x5c000000f0000011 0xe2e0000007800000

def z63 : W := mkw 0x24901f8000000000 0x012480fc00000000 0x00001f8000000008 0x000000fc00000000

def z64 : W := mkw 0x080b0058b0316306 0x00405802c5818b18 0x800f807cf039f394 0x34007c03e781cf9c

def z65 : W := mkw 0x5b6fe010edbe4204 0x0adb7f00876df210 0xfffff870ffffc21f 0xffffffc387fffe10

def z66 : W := mkw 0x0032a295b0fb77b6 0x80019514ad87dbbd 0x8071e78ff1ffffff 0x7c038f3c7f8fffff

def z67 : W := mkw 0xa4901fd81241ff1e 0x052480fec0920ff8 0x80001ffc0001ff88 0x140000ffe0000ffc

def z68 : W := mkw 0xb6d01fef5b41bc18 0x15b680ff7ada0de0 0xfff01fffffc1fc1b 0xffff80fffffe0fe0

def z69 : W := mkw 0xbedb1fd8fb71ff1e 0x05f6d8fec7db8ff8 0xffff9ffcfff9ff9f 0xfffffcffe7ffcffc

def z70 : W := mkw 0xb7d65fb2df65fe5d 0x05beb2fd96fb2ff2 0xfffe7ff3ffe7fe7f 0xfffff3ff9fff3ff3

def z71 : W := mkw 0x080b0000a0300000 0x0040580005018000 0x5c0f8000f0380015 0xe2e07c000781c000

def z72 : W := mkw 0xb2d00b804b409c18 0x0596805c025a04e0 0x23f001800fc00c02 0x091f800c007e0060

def z73 : W := mkw 0x7fdd5fea00000000 0x13feeaff50000000 0x7ffe1ff00000000b 0xc3fff0ff80000000

def z74 : W := mkw 0xb7d45fa25b41bc18 0x05bea2fd12da0de0 0xfffe7ff3ffc1fc1f 0xfffff3ff9ffe0fe0

def z75 : W := mkw 0x5366e000edbe0000 0x0a9b3700076df000 0x23f06000fffe0012 0x291f830007fff000

def z76 : W := mkw 0x5b6fe010fdbf6306 0x0adb7f0087edfb18 0xffffe000fffff397 0xefffff0007ffff9c

def z77 : W := mkw 0xf3f4eba74b409c18 0x179fa75d3a5a04e0 0x23f061830fc00c02 0x091f830c187e0060

def z78 : W := mkw 0x7ffdffef699a0000 0x1bffefff7b4cd000 0x7fffffff71d8000f 0xf3fffffffb8ec000

def z79 : W := mkw 0x0c39b6cd00000000 0x0061cdb668000000 0x5c7fffff0000000f 0xd2e3fffff8000000

def z80 : W := mkw 0xb6c01d005b01a808 0x05b600e802d80d40 0x7ff01800ffc1c013 0xebff80c007fe0e00

def z81 : W := mkw 0x5b7fe285edbe0000 0x0adbff142f6df000 0x7fffe78ffffe001f 0xfbffff3c7ffff000

def z82 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071860c01fe3ff1 0x2c038c30600ff1ff

def z83 : W := mkw 0x7fffffefa4be0000 0x1bffffff7d25f000 0x7fffffff003e000f 0xd3fffffff801f000

def z84 : W := mkw 0xb6f0bf855bcbbcb8 0x85b785fc2ade5de5 0xfff1ff8fffffffff 0xffff8ffc7fffffff

def z85 : W := mkw 0x0402145890216306 0x002010a2c4810b18 0x800e1e7c8021f39c 0xd40070f3e4010f9c

def z86 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e187000000000 0x811c70c380000000

def z87 : W := mkw 0x36d01f8000000000 0x01b680fc00000000 0x7ff01f800000000b 0xc3ff80fc00000000

def z88 : W := mkw 0x73f4eba700000000 0x139fa75d38000000 0x23f0618300000002 0x011f830c18000000

def z89 : W := mkw 0x5befe932efbeca45 0x0adf7f49977df652 0xfffff9f3ffffce7f 0xffffffcf9ffffe73

def z90 : W := mkw 0x0000000010012000 0x0000000000800900 0x80000000f001f010 0x2400000007800f80

def z91 : W := mkw 0x5b6fe06fedbe0000 0x1adb7f037f6df000 0x7fffe07ffffe0017 0xfbffff03fffff000

def z92 : W := mkw 0x5b7fe285edfe14b0 0x8adbff142f6ff0a5 0xffffe78ffffe3fff 0xffffff3c7ffff1ff

def z93 : W := mkw 0x5b4f4000ed340000 0x0ada7a000769a000 0x7f8e0000fe000000 0x83fc700007f00000

def z94 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff0038339f 0xf7fffffff801c19c

def z95 : W := mkw 0x0400145810016306 0x002000a2c0800b18 0x000018700001c000 0x000000c380000e00

def z96 : W := mkw 0xffffffffdf65fe5d 0x17fffffffefb2ff2 0xffffffffffe7fe7f 0xffffffffffff3ff3

def z97 : W := mkw 0xb650168059413418 0x05b280b402ca09a0 0x5c70060071c03001 0x22e38030038e0180

def z98 : W := mkw 0x24801d6a00000000 0x112400eb50000000 0x0000187000000000 0x000000c380000000

def z99 : W := mkw 0x00020010efbeca45 0x08001000877df652 0x80000000ffffce70 0x2c00000007fffe73

def z100 : W := mkw 0x0400145810016306 0x002000a2c0800b18 0x80001e7c0001f388 0x140000f3e0000f9c

def z101 : W := mkw 0x5364e0004d8e0000 0x0a9b2700026c7000 0x23f060000fc60002 0x091f8300007e3000

def z102 : W := mkw 0x25965fff8624ca45 0x112cb2fffc312652 0xa38e7fff8e27ce7e 0xdd1c73fffc713e73

def z103 : W := mkw 0x7ffdffef49000000 0x13ffefff7a480000 0x7fffffffffc0001f 0xfbfffffffffe0000

def z104 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xffffe60cfffe339f 0xffffff3067fff19c

def z105 : W := mkw 0x0186492284240000 0x000c324914212000 0x238e79f38e26001e 0xd91c73cf9c713000

def z106 : W := mkw 0x492fe000a4be0000 0x0a497f000525f000 0x000fe000003e0004 0x00007f000001f000

def z107 : W := mkw 0x0030a28500000000 0x0001851428000000 0x0071e78f0000000f 0x50038f3c78000000

def z108 : W := mkw 0xb7d65f80df65bc18 0x05beb2fc06fb2de0 0xfffe7f80ffe7fc1f 0xeffff3fc07ff3fe0

def z109 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071878f01d83fe9 0x34038c3c780ec1ff

def z110 : W := mkw 0x000200108624ca45 0x0000100084312652 0x000000008e01c000 0x0000000004700e00

def z111 : W := mkw 0x0000000000ca14b0 0x80000000000650a5 0x8000618301fe3ffe 0x7c00030c180ff1ff

def z112 : W := mkw 0x5a69a000699a0000 0x0ad34d00034cd000 0x7ff18000ffd80013 0xebff8c0007fec000

def z113 : W := mkw 0x7f7df6cd00000000 0x13fbefb668000000 0x7fffe60c00000007 0xc3ffff3060000000

def z114 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xffffe183fffe0e7f 0xffffff0c1ffff073

def z115 : W := mkw 0x7fffffffb0316306 0x13fffffffd818b18 0xfffffffff039f39f 0xf7ffffffff81cf9c

def z116 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80000000f039f390 0x240000000781cf9c

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001860c0000000d 0x50000c3060000000

def z118 : W := mkw 0x5b4d400000000000 0x02da6a0000000000 0x7f8e000000000000 0x83fc700000000000

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001800c00380384 0x10000c006001c01c

def z120 : W := mkw 0x5b6de06f00000000 0x12db6f0378000000 0x7fffe07f00000007 0xd3ffff03f8000000

def z121 : W := mkw 0xb6f0bf855bcbbcb8 0x85b785fc2ade5de5 0xfff07f83ffc7fc7b 0xefff83fc1ffe3fe3

def z122 : W := mkw 0x7fcf5d7ab0316306 0x13fe7aebd5818b18 0xff8f9e7cf039f39d 0xf7fc7cf3e781cf9c

def z123 : W := mkw 0x5b6fe005edbe00a0 0x8adb7f002f6df005 0x7fffe00ffffe03f7 0xfbffff007ffff01f

def z124 : W := mkw 0x000000100200ca45 0x0000000080100652 0x800000000001ce60 0x0400000000000e73

def z125 : W := mkw 0x0c0b145880204204 0x006058a2c4010210 0xdc0f9e7c8021c21d 0xd6e07cf3e4010e10

def z126 : W := mkw 0x4124e02700000000 0x1209270138000000 0x0000600300000000 0x0000030018000000

def z127 : W := mkw 0x0400140010012000 0x002000a000800900 0x5c00060070003001 0x22e0003003800180

def z128 : W := mkw 0x5b6fe032edbe4245 0x0adb7f01976df212 0x7fffe073fffe0277 0xfbffff039ffff013

def z129 : W := mkw 0x0010028000401410 0x00008014000200a0 0x8070078001c03c1b 0x6c03803c000e01e0

def z130 : W := mkw 0xb6d01f8059413418 0x05b680fc02ca09a0 0x7ff01f8071c0300b 0xe3ff80fc038e0180

def z131 : W := mkw 0x00100285004014b0 0x80008014280200a5 0x8000078f00003fe8 0x1400003c780001ff

def z132 : W := mkw 0x0126e03784ae42e5 0x80093701bc257217 0x000fe07f003e03e4 0x10007f03f801f01f

def z133 : W := mkw 0x73f4eba700000000 0x139fa75d38000000 0x23f1e78f0000000f 0x511f8f3c78000000

def z134 : W := mkw 0x0809000020100000 0x0040480001008000 0x5c01800070180001 0x22e00c000380c000

def z135 : W := mkw 0x0030a285008a0000 0x0001851428045000 0x0071e78f01fe001f 0x78038f3c780ff000

def z136 : W := mkw 0x4d2ff458b4bf6306 0x0a697fa2c5a5fb18 0xdc0ffe7cf03ff39d 0xf6e07ff3e781ff9c

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000618300260e7e 0x5c00030c18013073

def z138 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0f9e7cf019f181 0xa2e07cf3e780cf8c

def z139 : W := mkw 0x01b6ebb786eedef5 0x800db75dbc3776f7 0xa3ffffff8fffffff 0xfd1ffffffc7fffff

def z140 : W := mkw 0x00020000ed340000 0x080010000769a000 0x00000000fe000000 0x0000000007f00000

def z141 : W := mkw 0x77f4ffef00000000 0x13bfa7ff78000000 0x23f07fff0000000a 0x111f83fff8000000

def z142 : W := mkw 0x0002001080204204 0x0000100084010210 0x800000008021c210 0x0400000004010e10

def z143 : W := mkw 0x0d8d5d6a00000000 0x006c6aeb50000000 0x7f8fffff0000000f 0xd3fc7ffff8000000

def z144 : W := mkw 0x000000004d8e0000 0x08000000026c7000 0x000000000fc60000 0x08000000007e3000

def z145 : W := mkw 0x0000001000004204 0x0000000080000210 0x800018700001c208 0x140000c380000e10

def z146 : W := mkw 0x0104402204040041 0x0008220110202002 0x0000600300060060 0x0000030018003003

def z147 : W := mkw 0x492de06f008a00a0 0x92496f0378045005 0x000fe07f003e03e4 0x10007f03f801f01f

def z148 : W := mkw 0x0000000000ca14b0 0x80000000000650a5 0x8000000001fe3ff0 0x2c000000000ff1ff

def z149 : W := mkw 0x7e79b6cd00000000 0x13f3cdb668000000 0x5c71860c00000001 0x02e38c3060000000

def z150 : W := mkw 0x008009320200ca45 0x0004004990100652 0x000018700001c000 0x000000c380000e00

def z151 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0070618301c60c62 0x0803830c180e3063

def z152 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0e187000000000 0x82e070c380000000

def z153 : W := mkw 0x0030a285004014b0 0x80018514280200a5 0x8071e78f00003fef 0x54038f3c780001ff

def z154 : W := mkw 0x0030a28000ca1410 0x00018514000650a0 0x8071e78001fe3c1f 0x6c038f3c000ff1e0

def z155 : W := mkw 0x4829a04d00000000 0x12414d0268000000 0x0001800c00000000 0x00000c0060000000

def z156 : W := mkw 0x7e79b6cd00ca14b0 0x93f3cdb6680650a5 0x5c71860c01d83181 0x22e38c30600ec18c

def z157 : W := mkw 0xfffdffef1241bc18 0x17ffefff78920de0 0xffffffff0001fc0f 0xd7fffffff8000fe0

def z158 : W := mkw 0x7ffdffef008a0000 0x13ffefff78045000 0x7fffffff01fe001f 0xfbfffffff80ff000

def z159 : W := mkw 0x7270a28500000000 0x1393851428000000 0x0070000000000000 0x0003800000000000

def z160 : W := mkw 0x008209328220ca45 0x0004104994110652 0x800e19f38021ce7c 0xd40070cf9c010e73

def z161 : W := mkw 0x7fffffff86eedef5 0x93fffffffc3776f7 0xffffffff8fffffff 0xfffffffffc7fffff

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000060c00003388 0x140000306000019c

def z163 : W := mkw 0xb2f0ab854bca9cb8 0x8597855c2a5e54e5 0xa3f1e78f0ffe3fff 0x7d1f8f3c787ff1ff

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x238000008e000012 0xc91c000004700000

def z165 : W := mkw 0x0c09144830112102 0x006048a241808908 0x5c0f9e7c7018318d 0xf2e07cf3e380c18c

def z166 : W := mkw 0x0002001084244245 0x0000100084212212 0x0000000000260260 0x0000000000013013

def z167 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071878c01d83d9b 0x6c038c3c600ec1ec

def z168 : W := mkw 0x800000001241bc18 0x0400000000920de0 0x800000000001fc00 0x0400000000000fe0

def z169 : W := mkw 0x7fedfd6a00000000 0x13ff6feb50000000 0x7ffff87000000007 0xc3ffffc380000000

def z170 : W := mkw 0x0022a000edbe0000 0x08011500076df000 0x0071e000fffe0017 0x68038f0007fff000

def z171 : W := mkw 0x5befe922efbe8841 0x0adf7f49177df442 0x7fffe183fffe0c77 0xebffff0c1ffff063

def z172 : W := mkw 0x0000000030112102 0x0000000001808908 0x0000000070183180 0x200000000380c18c

def z173 : W := mkw 0x1a4b0000e9300000 0x00d2580007498000 0x7fff8000fff80017 0xebfffc0007ffc000

def z174 : W := mkw 0x5364e0004d8e0000 0x0a9b2700026c7000 0x7ff06000ffc60013 0xebff830007fe3000

def z175 : W := mkw 0x0c3bb6ddb0fb77b6 0x8061ddb6ed87dbbd 0xdc7f9e7cf1f9f39d 0xf6e3fcf3e78fcf9c

def z176 : W := mkw 0x01864932b635eb47 0x000c324995b1af5a 0xa38e79f3fe3ffffe 0xfd1c73cf9ff1ffff

def z177 : W := mkw 0x0184492206048841 0x000c224910302442 0x238061830e060c62 0x091c030c18703063

def z178 : W := mkw 0x0184492200000000 0x000c224910000000 0x2380618300000002 0x011c030c18000000

def z179 : W := mkw 0x080b0000a0300000 0x0040580005018000 0x000f800000380004 0x00007c000001c000

def z180 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38061838e27ce72 0x0d1c030c1c713e73

def z181 : W := mkw 0x0dbfffffb6fffff7 0x806dfffffdb7ffff 0xffffffffffffffff 0xffffffffffffffff

def z182 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff007807fc03c03 0x2bff803c03fe01e0

def z183 : W := mkw 0x008209108624ca45 0x0004104884312652 0xa38019808e27ce7a 0xcd1c00cc04713e73

def z184 : W := mkw 0x5b6de000008a0000 0x02db6f0000045000 0x7fffe00001fe0017 0xebffff00000ff000

def z185 : W := mkw 0x7f7ff6cdedbe0000 0x1bfbffb66f6df000 0x7fffe60cfffe0017 0xebffff3067fff000

def z186 : W := mkw 0x0002001086eedef5 0x80001000843776f7 0x800000008ffffff0 0x2c000000047fffff

def z187 : W := mkw 0xffffff80ffffbc18 0x0ffffffc07fffde0 0xffffff80fffffc1f 0xeffffffc07ffffe0

def z188 : W := mkw 0xb3d44ba24f449c59 0x059ea25d127a24e2 0x23f061830fc60c62 0x091f830c187e3063

def z189 : W := mkw 0x5a69a000699a0000 0x0ad34d00034cd000 0x5c71e00071fe0017 0x6ae38f00038ff000

def z190 : W := mkw 0x534440004d040000 0x0a9a220002682000 0x238000000e000000 0x011c000000700000

def z191 : W := mkw 0x0104402200000000 0x0008220110000000 0x000e607300000004 0x1000730398000000

def z192 : W := mkw 0xbefbbfddfbfbffbe 0x85f7ddfeefdfdffd 0xffffffffffffffff 0xffffffffffffffff

def z193 : W := mkw 0x49ade96f00000000 0x124d6f4b78000000 0x238ff9ff0000000e 0xd11c7fcff8000000

def z194 : W := mkw 0x492fe000a4be0000 0x0a497f000525f000 0x5c0fe000f03e0015 0xe2e07f000781f000

def z195 : W := mkw 0xb6d01f855b41bcb8 0x85b680fc2ada0de5 0xfff01f8fffc1fffb 0xffff80fc7ffe0fff

def z196 : W := mkw 0x01b4eba700ca14b0 0x800da75d380650a5 0xa3ffffff01fe3fff 0xfd1ffffff80ff1ff

def z197 : W := mkw 0x00020000a4be0000 0x080010000525f000 0x00000000003e0000 0x000000000001f000

def z198 : W := mkw 0x7fffffff8624ca45 0x13fffffffc312652 0xffffffff8e27ce7f 0xdffffffffc713e73

def z199 : W := mkw 0x0020a000008a0000 0x0001050000045000 0x0071800001d80001 0x20038c00000ec000

def z200 : W := mkw 0x0d8f5d7ab635eb47 0x006c7aebd5b1af5a 0xff8f9e7cfe39f39d 0xf7fc7cf3e7f1cf9c

def z201 : W := mkw 0xbedb1fd8fb71ff1e 0x05f6d8fec7db8ff8 0xfffe1ff0ffc1fc1b 0xeffff0ff87fe0fe0

def z202 : W := mkw 0x24901fef004014b0 0x912480ff780200a5 0x80001fff00003fe8 0x140000fff80001ff

def z203 : W := mkw 0x7e49144800000000 0x13f248a240000000 0x5c00000000000000 0x02e0000000000000

def z204 : W := mkw 0x008009320200ca45 0x0004004990100652 0x800019f30001ce68 0x140000cf98000e73

def z205 : W := mkw 0xfffdff805b41bc18 0x07ffeffc02da0de0 0xffffff80ffc1fc1f 0xeffffffc07fe0fe0

def z206 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff19f8cfff9ff9f 0xffff8cfc67ffcffc

def z207 : W := mkw 0x0c09144800000000 0x006048a240000000 0xdc0f9e7c0038339d 0xf6e07cf3e001c19c

def z208 : W := mkw 0x492fe058a4be4306 0x0a497f02c525f218 0x000fe07c003e0384 0x10007f03e001f01c

def z209 : W := mkw 0x0c0b1458a0304306 0x006058a2c5018218 0x5c0f9e7c0038038d 0xd2e07cf3e001c01c

def z210 : W := mkw 0x00020000edfe14b0 0x88001000076ff0a5 0x80000000fffe3ff0 0x2c00000007fff1ff

def z211 : W := mkw 0x00020010b635eb47 0x0000100085b1af5a 0x80000000fe3ffff0 0x2c00000007f1ffff

def z212 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc01860cf039f391 0x26e00c306781cf9c

def z213 : W := mkw 0xb6c01d005b01a808 0x05b600e802d80d40 0xff801980fe01cc1a 0xcffc00cc07f00e60

def z214 : W := mkw 0x0032a285edfe14b0 0x880195142f6ff0a5 0x8071e78ffffe3fff 0x7c038f3c7ffff1ff

def z215 : W := mkw 0x5b4f4000ed340000 0x0ada7a000769a000 0x7ffe0000ffc00013 0xebfff00007fe0000

def z216 : W := mkw 0x7fffffffa0304306 0x13fffffffd018218 0x7fffffff0038038f 0xd3fffffff801c01c

def z217 : W := mkw 0x0c09144810012000 0x006048a240800900 0xdc0f9e7cf001f01d 0xf6e07cf3e7800f80

def z218 : W := mkw 0x0184492200000000 0x000c224910000000 0xa38e79f300260e7e 0xdd1c73cf98013073

def z219 : W := mkw 0x00020010a0304306 0x0000100085018218 0x0000000000380380 0x000000000001c01c

def z220 : W := mkw 0x0c09144830112102 0x006048a241808908 0xdc019e0cf019f199 0xe6e00cf06780cf8c

def z221 : W := mkw 0x0430b68510cb34b0 0x802185b4288659a5 0xdc71ff8ff1ffffff 0xfee38ffc7f8fffff

def z222 : W := mkw 0x4d2ff47fb0316306 0x12697fa3fd818b18 0xdc0ffe7ff039f39d 0xf6e07ff3ff81cf9c

def z223 : W := mkw 0x080b0058a0304306 0x00405802c5018218 0x800f987c8039c39c 0xd4007cc3e401ce1c

def z224 : W := mkw 0x7ffdffff10016306 0x13ffeffff8800b18 0xffffffff0001f38f 0xd7fffffff8000f9c

def z225 : W := mkw 0x0186493280204204 0x000c324994010210 0xa38e79f38021c21e 0xd51c73cf9c010e10

def z226 : W := mkw 0x0186490086248800 0x000c324804312440 0xa38e79808e27cc1e 0xcd1c73cc04713e60

def z227 : W := mkw 0x2c991fef00000000 0x1164c8ff78000000 0x5c0f9fff0000000d 0xd2e07cfff8000000

def z228 : W := mkw 0xfffdffef5bcbbcb8 0x97ffefff7ade5de5 0xffffffffffffffff 0xffffffffffffffff

def z229 : W := mkw 0x73f4eba700ca14b0 0x939fa75d380650a5 0x23f0618301c60c62 0x091f830c180e3063

def z230 : W := mkw 0x800000005b01a808 0x0400000002d80d40 0x00000000fe01c000 0x0000000007f00e00

def z231 : W := mkw 0x0032a29586eedef5 0x80019514ac3776f7 0x8071e78f8fffffff 0x7c038f3c7c7fffff

def z232 : W := mkw 0xf7f4ffa75b41bc18 0x17bfa7fd3ada0de0 0xfff07f83ffc1fc1b 0xefff83fc1ffe0fe0

def z233 : W := mkw 0x36f0bf8500000000 0x01b785fc28000000 0x7ff1ff8f0000000f 0xd3ff8ffc78000000

def z234 : W := mkw 0x0c09144830112102 0x006048a241808908 0x5c00000070000000 0x02e0000003800000

def z235 : W := mkw 0x0c09145830116306 0x006048a2c1808b18 0xdc019e7c7019f389 0x36e00cf3e380cf9c

def z236 : W := mkw 0x7fffffefedfe14b0 0x9bffffff7f6ff0a5 0xfffffffffffe3fff 0xfffffffffffff1ff

def z237 : W := mkw 0x924000005b41bc18 0x0492000002da0de0 0xfff00000ffc1fc13 0xefff800007fe0fe0

def z238 : W := mkw 0x0020a00000000000 0x0001050000000000 0x0071e00000000007 0x40038f0000000000

def z239 : W := mkw 0x1e4b1458f9316306 0x00f258a2c7c98b18 0xffff9e7cfff9f39f 0xfffffcf3e7ffcf9c

def z240 : W := mkw 0x36d01f8002008800 0x01b680fc00100440 0xfff01f808e01cc1b 0xcfff80fc04700e60

def z241 : W := mkw 0x0126e00084ae0000 0x0009370004257000 0x23ffe0008ffe0017 0xe91fff00047ff000

def z242 : W := mkw 0x0d8f5d7a8624ca45 0x006c7aebd4312652 0xff8fffff8e27ce7f 0xdffc7ffffc713e73

def z243 : W := mkw 0x7fcf5d7ab0316306 0x13fe7aebd5818b18 0x7f8e1870f001c000 0x83fc70c387800e00

def z244 : W := mkw 0x080b0000a0300000 0x0040580005018000 0xdc0f860cf038339d 0xf6e07c306781c19c

def z245 : W := mkw 0x5b6fe000ed340000 0x0adb7f000769a000 0x7fffe000fe000007 0xc3ffff0007f00000

def z246 : W := mkw 0x7ffdffef06048841 0x13ffefff78302442 0x7fffffff0e060c6f 0xdbfffffff8703063

def z247 : W := mkw 0xb650168059413418 0x05b280b402ca09a0 0xdc701e00f1c1f019 0xe6e380f0078e0f80

def z248 : W := mkw 0x0000003200004245 0x0000000190000212 0x0000007300000260 0x1000000398000013

def z249 : W := mkw 0x0000000006048841 0x0000000000302442 0x000000000e060c60 0x0800000000703063

def z250 : W := mkw 0xa0900b8002409c18 0x0504805c001204e0 0x0000018000000c00 0x0000000c00000060

def z251 : W := mkw 0x493de2ef00ca14b0 0x9249ef17780650a5 0x807fe7ff01fe3fff 0x7c03ff3ff80ff1ff

def z252 : W := mkw 0x1270a28549ca14b0 0x809385142a4e50a5 0xfff1e78ffffe3fff 0xffff8f3c7ffff1ff

def z253 : W := mkw 0x13c64932cf24ca45 0x009e324996792652 0xfffe79f3ffe7ce7f 0xfffff3cf9fff3e73

def z254 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7ffe6000ffc60002 0x8bfff30007fe3000

def z255 : W := mkw 0x0010028000000000 0x0000801400000000 0x007007800000000b 0x4003803c00000000

def z256 : W := mkw 0x36d01f8049000000 0x01b680fc02480000 0x7ff01f80ffc0001b 0xebff80fc07fe0000

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z258 : W := mkw 0x083ba2dda0fa57b6 0x8041dd16ed07d2bd 0x807fe7ff01fe3fff 0x7c03ff3ff80ff1ff

def z259 : W := mkw 0xb2d00b804b409c18 0x0596805c025a04e0 0xa3f019808fc1cc1a 0xcd1f80cc047e0e60

def z260 : W := mkw 0xfffdffef59413418 0x17ffefff7aca09a0 0x7fffffff71c0300f 0xf3fffffffb8e0180

def z261 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x800f9e7c0039f38c 0x14007cf3e001cf9c

def z262 : W := mkw 0x082ba000a0ba0000 0x00415d000505d000 0x5c7fe000f1fe0017 0xeae3ff00078ff000

def z263 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0e1870f039f390 0xa6e070c38781cf9c

def z264 : W := mkw 0x5b6de0004d8e0000 0x0adb6f00026c7000 0x7fffe0000fc60007 0xcbffff00007e3000

def z265 : W := mkw 0xbecb1d58fb31eb0e 0x05f658eac7d98f58 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z266 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38fffff8e3fffff 0xfd1c7ffffc71ffff

def z267 : W := mkw 0x0080090002008800 0x0004004800100440 0xa38079838e27ce7e 0xdd1c03cc1c713e73

def z268 : W := mkw 0x090f4000a4340000 0x00487a000521a000 0x7f8fe000fe3e0017 0xebfc7f0007f1f000

def z269 : W := mkw 0x0002000084240000 0x0000100004212000 0x000000008e260010 0x0800000004713000

def z270 : W := mkw 0x0400140000000000 0x002000a000000000 0x5c001e0000000009 0xc2e000f000000000

def z271 : W := mkw 0xffffff85ffffbcb8 0x8ffffffc2ffffde5 0xffffff8fffffffff 0xfffffffc7fffffff

def z272 : W := mkw 0x7fffffffb0fb77b6 0x93fffffffd87dbbd 0xfffffffff1ffffff 0xffffffffff8fffff

def z273 : W := mkw 0x7e79b6cd699a0000 0x1bf3cdb66b4cd000 0x5c71860c71d80001 0x22e38c30638ec000

def z274 : W := mkw 0x37d65fb28624ca45 0x01beb2fd94312652 0xfffe7ff38e27ce7f 0xdffff3ff9c713e73

def z275 : W := mkw 0x24901fff0200ca45 0x112480fff8100652 0x80001fff0001ce68 0x140000fff8000e73

def z276 : W := mkw 0x0c0b1458b635eb47 0x006058a2c5b1af5a 0xdc0f9e7cfe3ffffd 0xfee07cf3e7f1ffff

def z277 : W := mkw 0x7e79b6cd00000000 0x13f3cdb668000000 0x5c7f9e7c0000000d 0xd2e3fcf3e0000000

def z278 : W := mkw 0x00000000008a00a0 0x8000000000045005 0x00000000003e03e0 0x000000000001f01f

def z279 : W := mkw 0x00b0abb702cadef5 0x8005855db81656f7 0x8071ffff01ffffff 0x7c038ffff80fffff

def z280 : W := mkw 0x73f6ebb78624ca45 0x139fb75dbc312652 0xa3fe79f38e27ce7e 0xdd1ff3cf9c713e73

def z281 : W := mkw 0x5b6de0006d9e0000 0x0adb6f00036cf000 0x7ff1e0007fde0003 0x2bff8f0003fef000

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000020021c 0x5400000000010010

def z283 : W := mkw 0x0106400084240000 0x0008320004212000 0x238e00008e000000 0x811c700004700000

def z284 : W := mkw 0xffdf5f80ff75bc18 0x0ffefafc07fbade0 0xfffe1f80ffc1fc1b 0xeffff0fc07fe0fe0

def z285 : W := mkw 0xbe5b16d8f971771e 0x05f2d8b6c7cb8bb8 0xdc7f9e7cf1f9f39d 0xf6e3fcf3e78fcf9c

def z286 : W := mkw 0x0000000049000000 0x0000000002480000 0x00000000ffc00010 0x2800000007fe0000

def z287 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8f9e7c0000000d 0xd3fc7cf3e0000000

def z288 : W := mkw 0x7ffdffef30112102 0x13ffefff79808908 0x7fffffff7018318f 0xf3fffffffb80c18c

def z289 : W := mkw 0x13464000cd240000 0x009a320006692000 0x7ffe6000ffe60017 0xebfff30007ff3000

def z290 : W := mkw 0x7e79b6cd30112102 0x13f3cdb669808908 0x5c71860c70183181 0x22e38c306380c18c

def z291 : W := mkw 0xb6d01f801241bc18 0x05b680fc00920de0 0xfff01f800001fc0b 0xc7ff80fc00000fe0

def z292 : W := mkw 0xdb6fe000ffffbc18 0x0edb7f0007fffde0 0xffffe000fffffc17 0xefffff0007ffffe0

def z293 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7f8fe000fe3e0004 0x83fc7f0007f1f000

def z294 : W := mkw 0x7ffdffef10012000 0x13ffefff78800900 0xfffffffff001f01f 0xf7ffffffff800f80

def z295 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fffffff01d8318f 0xf3fffffff80ec18c

def z296 : W := mkw 0x53e6e932cfaeca45 0x0a9f3749967d7652 0xa3fe79f38fe7ce7e 0xdd1ff3cf9c7f3e73

def z297 : W := mkw 0xfffffffffb71ff1e 0x17ffffffffdb8ff8 0xfffffffffff9ff9f 0xffffffffffffcffc

def z298 : W := mkw 0x01b6ebb786eedef5 0x800db75dbc3776f7 0xa3fe79f38fe7ce7e 0xdd1ff3cf9c7f3e73

def z299 : W := mkw 0x0020a00500000000 0x0001050028000000 0x0001e00f00000004 0x10000f0078000000

def z300 : W := mkw 0x493de2ef00000000 0x1249ef1778000000 0x007fe7ff0000000f 0x5003ff3ff8000000

def z301 : W := mkw 0x808009005b41bc18 0x0404004802da0de0 0xa3801980ffc1fc1a 0xed1c00cc07fe0fe0

def z302 : W := mkw 0xa4901f805b41bc18 0x052480fc02da0de0 0x80001f80ffc1fc18 0x2c0000fc07fe0fe0

def z303 : W := mkw 0x0030a28500401410 0x00018514280200a0 0x8071e78f01c03c1f 0x7c038f3c780e01e0

def z304 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0f9870f039c015 0xe2e07cc38781ce00

def z305 : W := mkw 0x492fe000a4be0000 0x0a497f000525f000 0x238fe0008e3e0016 0xc91c7f000471f000

def z306 : W := mkw 0xb3d64bb2cf64de5d 0x059eb25d967b26f2 0xa3fe79f38fe7ce7e 0xdd1ff3cf9c7f3e73

def z307 : W := mkw 0x0106401084244204 0x0008320084212210 0xa38e78708e27c21e 0xdd1c73c384713e10

def z308 : W := mkw 0x6dbdffef00000000 0x136defff78000000 0x000fffff0000000c 0x10007ffff8000000

def z309 : W := mkw 0x0010028000401410 0x00008014000200a0 0x0070060001c03001 0x20038030000e0180

def z310 : W := mkw 0xb6d21f90df65fe5d 0x05b690fc86fb2ff2 0xfff01f80ffe7fe7b 0xefff80fc07ff3ff3

def z311 : W := mkw 0x840014005b41bc18 0x042000a002da0de0 0xdc001e00ffc1fc19 0xeee000f007fe0fe0

def z312 : W := mkw 0x5b6fe000a4be0000 0x0adb7f000525f000 0x7fffe000003e0007 0xc3ffff000001f000

def z313 : W := mkw 0x0400140010012000 0x002000a000800900 0x5c001800f001c000 0x82e000c007800e00

def z314 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fff8000ffd80001 0xa3fffc0007fec000

def z315 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e18708e21c21c 0xd51c70c384710e10

def z316 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e19f38e01ce68 0x951c70cf9c700e73

def z317 : W := mkw 0x5bcf4932ef34ca45 0x0ade7a499779a652 0xff8e79f3fe27ce7e 0xdffc73cf9ff13e73

def z318 : W := mkw 0x492fe000edbe0000 0x0a497f00076df000 0x000fe000fffe0014 0x28007f0007fff000

def z319 : W := mkw 0x00900bb70240def5 0x8004805db81206f7 0x80001fff0001ffe8 0x140000fff8000fff

def z320 : W := mkw 0x0010028500000000 0x0000801428000000 0x0000078f00000008 0x1000003c78000000

def z321 : W := mkw 0x5befe922edbe0000 0x0adf7f49176df000 0x7ffff9f3fffe001f 0xfbffffcf9ffff000

def z322 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x5c7fe00071fe0005 0x22e3ff00038ff000

def z323 : W := mkw 0x5b7fe280edfe1410 0x0adbff14076ff0a0 0xffffe780fffe3c1f 0xefffff3c07fff1e0

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x800018008001c018 0xc40000c004000e00

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001e78f003e3fff 0x7c000f3c7801f1ff

def z326 : W := mkw 0x801002805b41bc18 0x0400801402da0de0 0x80700780ffc1fc1b 0x6c03803c07fe0fe0

def z327 : W := mkw 0x5b6fe010efbeca45 0x0adb7f00877df652 0xffffe000ffffce77 0xefffff0007fffe73

def z328 : W := mkw 0x0010028000401410 0x00008014000200a0 0x8071878c01f83f9f 0x7c038c3c600fc1fc

def z329 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e79f38e07cc62 0x891c73cf9c703e63

def z330 : W := mkw 0x73c4492200000000 0x139e224910000000 0x2380000000000000 0x011c000000000000

def z331 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff01e00ffc1f001 0xa3ff80f007fe0f80

def z332 : W := mkw 0x36c01d0000000000 0x01b600e800000000 0x7f80180000000000 0x83fc00c000000000

def z333 : W := mkw 0x492fe000a4be0000 0x0a497f000525f000 0x007fe00001fe0017 0x6803ff00000ff000

def z334 : W := mkw 0x7ffdffef004014b0 0x93ffefff780200a5 0xffffffff00003fef 0xd7fffffff80001ff

def z335 : W := mkw 0xb6d01fb25b41fe5d 0x05b680fd92da0ff2 0xfff01ff3ffc1fe7b 0xffff80ff9ffe0ff3

def z336 : W := mkw 0xbedb1f80fb71bc18 0x05f6d8fc07db8de0 0xffff9f80fff9fc1f 0xeffffcfc07ffcfe0

def z337 : W := mkw 0x7ffdffef4d8e0000 0x1bffefff7a6c7000 0x7fffffff0fc6000f 0xdbfffffff87e3000

def z338 : W := mkw 0xbed91fc85b41bc18 0x05f6c8fe42da0de0 0xffff9ffcffc1fc1f 0xfffffcffe7fe0fe0

def z339 : W := mkw 0xfe79b6cd59413418 0x17f3cdb66aca09a0 0x5c71860c71c03001 0x22e38c30638e0180

def z340 : W := mkw 0x0010028000401410 0x00008014000200a0 0x8000078000003c08 0x0400003c000001e0

def z341 : W := mkw 0x080b0058a0304306 0x00405802c5018218 0x5c0f807cf0380395 0xf2e07c03e781c01c

def z342 : W := mkw 0x0400140010012000 0x002000a000800900 0x80001e000001f008 0x040000f000000f80

def z343 : W := mkw 0x492fe032a4be4245 0x0a497f019525f212 0x000fe073003e0264 0x10007f039801f013

def z344 : W := mkw 0x80020010df65fe5d 0x0400100086fb2ff2 0x80000000ffe7fe70 0x2c00000007ff3ff3

def z345 : W := mkw 0x81864932df65fe5d 0x040c324996fb2ff2 0xa38e79f3ffe7fe7e 0xfd1c73cf9fff3ff3

def z346 : W := mkw 0x7ef9bfef00000000 0x13f7cdff78000000 0x5c719fff00000009 0x12e38cfff8000000

def z347 : W := mkw 0x0000000000ca14b0 0x80000000000650a5 0x8001860c01fe3ffd 0x7c000c30600ff1ff

def z348 : W := mkw 0x5364e0004d8e0000 0x0a9b2700026c7000 0x23f1e0000ffe0017 0x691f8f00007ff000

def z349 : W := mkw 0x0104400000000000 0x0008220000000000 0x238e600000000006 0xc11c730000000000

def z350 : W := mkw 0x0000000002008800 0x0000000000100440 0x800000008e01cc10 0x0c00000004700e60

def z351 : W := mkw 0x0400144800000000 0x002000a240000000 0x00001e7c00000008 0x100000f3e0000000

def z352 : W := mkw 0xffcf5d00ff35a808 0x0ffe7ae807f9ad40 0x7f8e1800fe01c000 0x83fc70c007f00e00

def z353 : W := mkw 0xb6d01f805b01a808 0x05b680fc02d80d40 0x7ff01f80fe01c00b 0xc3ff80fc07f00e00

def z354 : W := mkw 0x0080092200000000 0x0004004910000000 0x000019f300000008 0x100000cf98000000

def z355 : W := mkw 0x7e79b6cd00ca14b0 0x93f3cdb6680650a5 0xdc71e78f01fe3fff 0x7ee38f3c780ff1ff

def z356 : W := mkw 0x49afe97f8624ca45 0x124d7f4bfc312652 0xa38ff9ff8e27ce7e 0xdd1c7fcffc713e73

def z357 : W := mkw 0x0d8f5d7ab635eb47 0x006c7aebd5b1af5a 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z358 : W := mkw 0x36d01f8000401410 0x01b680fc000200a0 0xfff01f8001c03c1b 0xefff80fc000e01e0

def z359 : W := mkw 0x490d406a00000000 0x12486a0350000000 0x000e007000000000 0x0000700380000000

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000618300060c62 0x0800030c18003063

def z361 : W := mkw 0x5f6df44800000000 0x02fb6fa240000000 0x7ffffe7c0000000f 0xd3fffff3e0000000

def z362 : W := mkw 0x4d2df46f00000000 0x12696fa378000000 0x5c0ffe7f0000000d 0xd2e07ff3f8000000

def z363 : W := mkw 0x0010028000401410 0x00008014000200a0 0x0070018001c00c02 0x0803800c000e0060

def z364 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0f987cf039c384 0x92e07cc3e781ce1c

def z365 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071e78f01d8318f 0x70038f3c780ec18c

def z366 : W := mkw 0xb6f0bf855bcbbcb8 0x85b785fc2ade5de5 0xfff19f8cffd9fd9b 0xefff8cfc67fecfec

def z367 : W := mkw 0xa4b0bf8512cbbcb8 0x852585fc28965de5 0x8071ff8f01ffffff 0x7c038ffc780fffff

def z368 : W := mkw 0x0402141090216204 0x002010a084810b10 0xdc0e1e70f021f21d 0xf6e070f387810f90

def z369 : W := mkw 0x2c9b1fffb0316306 0x1164d8fffd818b18 0xdc0f9ffff039f39d 0xf6e07cffff81cf9c

def z370 : W := mkw 0xa410168010413418 0x052080b4008209a0 0x0000060000003000 0x0000003000000180

def z371 : W := mkw 0xb2c009004b008808 0x0596004802580440 0x238000000e000000 0x011c000000700000

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000383390 0x240000000001c19c

def z373 : W := mkw 0x018449320200ca45 0x000c224990100652 0xa38e79f30001ce6e 0xd51c73cf98000e73

def z374 : W := mkw 0x0184492206048841 0x000c224910302442 0x238e79f30e060c6e 0xd91c73cf98703063

def z375 : W := mkw 0x492de00000000000 0x02496f0000000000 0x000fe00000000004 0x00007f0000000000

def z376 : W := mkw 0x04021410b0316306 0x002010a085818b18 0xdc001e00f039f399 0xe6e000f00781cf9c

def z377 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e79f30000000e 0xd3fc73cf98000000

def z378 : W := mkw 0xb7d45fa25f45bc59 0x05bea2fd12fa2de2 0xfff07f83ffc7fc7b 0xefff83fc1ffe3fe3

def z379 : W := mkw 0x0030a28500000000 0x0001851428000000 0x8071e78f00260e7f 0x5c038f3c78013073

def z380 : W := mkw 0xb6d01f804b409c18 0x05b680fc025a04e0 0x7ff01f800fc00c0b 0xcbff80fc007e0060

def z381 : W := mkw 0x0000000000ca14b0 0x80000000000650a5 0x0000000001c60c60 0x08000000000e3063

def z382 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x8001860cf039f39d 0x74000c306781cf9c

def z383 : W := mkw 0x800000005bcbbcb8 0x8400000002de5de5 0x80000000fffffff0 0x2c00000007ffffff

def z384 : W := mkw 0x080b0010a0304204 0x0040580085018210 0xdc0f9870f039c21d 0xf6e07cc38781ce10

def z385 : W := mkw 0x01b4eba700000000 0x000da75d38000000 0x23ffffff0000000f 0xd11ffffff8000000

def z386 : W := mkw 0x010640328624ca45 0x0008320194312652 0x800e60738e27ce74 0x1c0073039c713e73

def z387 : W := mkw 0x0106400084240000 0x0008320004212000 0x000e600000260004 0x0000730000013000

def z388 : W := mkw 0x5b7fe285edfe14b0 0x8adbff142f6ff0a5 0x7fffe60cfffe3197 0xebffff3067fff18c

def z389 : W := mkw 0x0030a28500000000 0x0001851428000000 0x8071e78f0038339f 0x74038f3c7801c19c

def z390 : W := mkw 0x0000000000ca14b0 0x80000000000650a5 0x0000000001d83180 0x20000000000ec18c

def z391 : W := mkw 0x0186493286eedef5 0x800c3249943776f7 0xa38e79f38ffffffe 0xfd1c73cf9c7fffff

def z392 : W := mkw 0x7fcf5d7a8624ca45 0x13fe7aebd4312652 0x7f8e18708e01c000 0x83fc70c384700e00

def z393 : W := mkw 0x5befe9328624ca45 0x02df7f4994312652 0xfffff9f38e27ce7f 0xdfffffcf9c713e73

def z394 : W := mkw 0xbecb1d58fb31eb0e 0x05f658eac7d98f58 0xff8f9e7cfe39f39d 0xf7fc7cf3e7f1cf9c

def z395 : W := mkw 0x3edb1fd8b0316306 0x01f6d8fec5818b18 0xffff9ffcf039f39f 0xf7fffcffe781cf9c

def z396 : W := mkw 0x018649328624ca45 0x000c324994312652 0x800e79f30027ce6c 0x140073cf98013e73

def z397 : W := mkw 0x0d8f5d7ab635eb47 0x006c7aebd5b1af5a 0xff8e79f3fe27ce7e 0xdffc73cf9ff13e73

def z398 : W := mkw 0x1240000049000000 0x0092000002480000 0x7f800000fe000000 0x83fc000007f00000

def z399 : W := mkw 0x0136e28584ee14b0 0x8009b7142c2770a5 0xa3ffe78f8ffe3fff 0xfd1fff3c7c7ff1ff

def z400 : W := mkw 0xffffffb2fffffe5d 0x0ffffffd97fffff2 0xfffffff3fffffe7f 0xffffffff9ffffff3

def z401 : W := mkw 0x5b6fe058edbe4306 0x0adb7f02c76df218 0x7fffe07cfffe0397 0xfbffff03e7fff01c

def z402 : W := mkw 0x36d01fef00000000 0x11b680ff78000000 0x7ff01fff0000000b 0xd3ff80fff8000000

def z403 : W := mkw 0x0106403284244245 0x0008320194212212 0x800e61f300260e7e 0x5c00730f98013073

def z404 : W := mkw 0x01b4eba706ce9cf1 0x800da75d383674e7 0xa3f1e78f0ffe3fff 0x7d1f8f3c787ff1ff

def z405 : W := mkw 0x0020a005008a00a0 0x8001050028045005 0x8001e60f003e33fd 0x74000f307801f19f

def z406 : W := mkw 0xb6c01d005b41bc18 0x05b600e802da0de0 0xff801800ffc1fc10 0xaffc00c007fe0fe0

def z407 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071860c01f8339d 0x74038c30600fc19c

def z408 : W := mkw 0x041016dd104177b6 0x802080b6e8820bbd 0x80001fff0001ffe8 0x140000fff8000fff

def z409 : W := mkw 0x1240000000000000 0x0092000000000000 0x7ff0000000000003 0xc3ff800000000000

def z410 : W := mkw 0x00900b8002409c10 0x0004805c001204e0 0xa3f01f808fc1fc1b 0xed1f80fc047e0fe0

def z411 : W := mkw 0xb6d21f90fb71ff1e 0x05b690fc87db8ff8 0xfff01f80fff9ff9b 0xefff80fc07ffcffc

def z412 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x23ffe0000ffe0006 0x091fff00007ff000

def z413 : W := mkw 0xb2d00b805b41bc18 0x0596805c02da0de0 0xa3f00180ffc1fc12 0x2d1f800c07fe0fe0

def z414 : W := mkw 0x0030a28500000000 0x0001851428000000 0x0070618300000002 0x0003830c18000000

def z415 : W := mkw 0x0000005800004306 0x00000002c0000218 0x0000007c00000380 0x10000003e000001c

def z416 : W := mkw 0x1240000049000000 0x0092000002480000 0x5c70000071c00001 0x22e38000038e0000

def z417 : W := mkw 0x7fffffffb0316306 0x13fffffffd818b18 0x7ffffffff001c00f 0xd3ffffffff800e00

def z418 : W := mkw 0x12c009004b008800 0x0096004802580440 0xfff01980ffc1cc1b 0xefff80cc07fe0e60

def z419 : W := mkw 0xa4901fb21241fe5d 0x052480fd90920ff2 0x80001ff30001fe68 0x140000ff98000ff3

def z420 : W := mkw 0x0020a005008a00a0 0x8001050028045005 0x0071e00f01fe03f7 0x78038f00780ff01f

def z421 : W := mkw 0x01a6e93286aeca45 0x000d374994357652 0xa3fff9f38fffce7f 0xfd1fffcf9c7ffe73

def z422 : W := mkw 0xbfdf5ffaff75ff5f 0x05fefaffd7fbaffa 0xffffffffffffffff 0xffffffffffffffff

def z423 : W := mkw 0x5bede92200000000 0x02df6f4910000000 0x7ffff9f30000000f 0xd3ffffcf98000000

def z424 : W := mkw 0x0106403284244245 0x0008320194212212 0x800e78738027c27c 0xd40073c39c013e13

def z425 : W := mkw 0x7fffff80edbe0000 0x0bfffffc076df000 0x7fffff80fffe001f 0xebfffffc07fff000

def z426 : W := mkw 0x0020a005008a00a0 0x8001050028045005 0x0000600300060060 0x0000030018003003

def z427 : W := mkw 0x5b6de000699a0000 0x0adb6f00034cd000 0x7fffe00071d80007 0xe3ffff00038ec000

def z428 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0070000001c00000 0x00038000000e0000

def z429 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e61f30e260e66 0x191c730f98713073

def z430 : W := mkw 0x7bfdebef00000000 0x13dfef5f78000000 0x23ffe1ff00000006 0x111fff0ff8000000

def z431 : W := mkw 0x04021458b0316306 0x002010a2c5818b18 0x80001e7cf039f398 0x340000f3e781cf9c

def z432 : W := mkw 0x1640140059012000 0x00b200a002c80900 0xfff01e00ffc1f01b 0xefff80f007fe0f80

def z433 : W := mkw 0x0020a00000ca14b0 0x80010500000650a5 0x8071e00001fe3ff7 0x6c038f00000ff1ff

def z434 : W := mkw 0x083ba285a0fa14b0 0x8041dd142d07d0a5 0xdc7fe78ff1fe3fff 0xfee3ff3c7f8ff1ff

def z435 : W := mkw 0x5b6fe000edfe14b0 0x8adb7f00076ff0a5 0xffffe000fffe3ff7 0xefffff0007fff1ff

def z436 : W := mkw 0x7f7df6ef00000000 0x13fbefb778000000 0x5c7fe67f00000005 0x12e3ff33f8000000

def z437 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071e78f01c60c6f 0x58038f3c780e3063

def z438 : W := mkw 0xf3f4eb804fce9c18 0x0f9fa75c027e74e0 0x23f061800fc60c02 0x091f830c007e3060

def z439 : W := mkw 0x080b0058a0304306 0x00405802c5018218 0x000e007000000000 0x0000700380000000

def z440 : W := mkw 0x5f4f5458fd356306 0x0afa7aa2c7e9ab18 0xff8f9e7cfe39f39d 0xf7fc7cf3e7f1cf9c

def z441 : W := mkw 0x00020000a0300000 0x0000100005018000 0x00000000f0380010 0x200000000781c000

def z442 : W := mkw 0x0080090002008800 0x0004004800100440 0x800019800001cc08 0x040000cc00000e60

def z443 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800061838e27ce7e 0x5c00030c1c713e73

def z444 : W := mkw 0x7ffdffef00401410 0x13ffefff780200a0 0xffffffff01c03c1f 0xfffffffff80e01e0

def z445 : W := mkw 0x0020a005008a00a0 0x8001050028045005 0x8001e18f003e0ffe 0x5c000f0c7801f07f

def z446 : W := mkw 0x492fe06fa4be0000 0x1a497f037d25f000 0x000fe07f003e0004 0x10007f03f801f000

def z447 : W := mkw 0xb2d00b804b409c18 0x0596805c025a04e0 0xa3f007800fc03c1b 0x6d1f803c007e01e0

def z448 : W := mkw 0x0000001010016306 0x0000000080800b18 0x800000000001f380 0x0400000000000f9c

def z449 : W := mkw 0xb6d01fd85b41ff1e 0x05b680fec2da0ff8 0xfff01ffcffc1ff9b 0xffff80ffe7fe0ffc

def z450 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff07f83ffe7fe7f 0xffff83fc1fff3ff3

def z451 : W := mkw 0x24b0bfef00ca14b0 0x912585ff780650a5 0x8071ffff01fe3fff 0x7c038ffff80ff1ff

def z452 : W := mkw 0x0010028000ca14b0 0x80008014000650a5 0x8070078001fe3ffb 0x6c03803c000ff1ff

def z453 : W := mkw 0x5bffebb7effedef5 0x8adfff5dbf7ff6f7 0xffffffffffffffff 0xffffffffffffffff

def z454 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0e1870f021c21c 0xd6e070c387810e10

def z455 : W := mkw 0x8c0b1458fb71ff1e 0x046058a2c7db8ff8 0xdc0f9e7cfff9ff9d 0xfee07cf3e7ffcffc

def z456 : W := mkw 0xffffffefffffbc18 0x1fffffff7ffffde0 0xfffffffffffffc1f 0xffffffffffffffe0

def z457 : W := mkw 0x5f7ff6ddfdff77b6 0x8afbffb6efeffbbd 0xffffffffffffffff 0xffffffffffffffff

def z458 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e78738e27c264 0x911c73c39c713e13

def z459 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xdc701f8071c1fc09 0x26e380fc038e0fe0

def z460 : W := mkw 0x7bfdeba700000000 0x13dfef5d38000000 0x7fffe18300000007 0xc3ffff0c18000000

def z461 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffe79f300000002 0x83fff3cf98000000

def z462 : W := mkw 0x12420000edbe0000 0x08921000076df000 0x7ff00000fffe0013 0xebff800007fff000

def z463 : W := mkw 0x36d01f8010012000 0x01b680fc00800900 0xfff01f80f001f01b 0xe7ff80fc07800f80

def z464 : W := mkw 0xa4901f851241bcb8 0x852480fc28920de5 0x80001f8f0001ffe8 0x140000fc78000fff

def z465 : W := mkw 0x0000006f00000000 0x1000000378000000 0x0000007f00000000 0x10000003f8000000

def z466 : W := mkw 0x00020010fdbf6306 0x0800100087edfb18 0x80000000fffff390 0x2c00000007ffff9c

def z467 : W := mkw 0x5f6ff448edbe0000 0x0afb7fa2476df000 0x7ffffe7cfffe001f 0xfbfffff3e7fff000

def z468 : W := mkw 0x7fcf5d7a8624ca45 0x13fe7aebd4312652 0xff8e79f38e27ce7e 0xdffc73cf9c713e73

def z469 : W := mkw 0x492fe005a4be00a0 0x8a497f002d25f005 0x000fe00f003e03e4 0x10007f007801f01f

def z470 : W := mkw 0x0020a00500ca14b0 0x80010500280650a5 0x8001e00f01fe3ff4 0x3c000f00780ff1ff

def z471 : W := mkw 0x5a6ba000e9ba0000 0x0ad35d00074dd000 0x5c7f8000f1f80015 0xe2e3fc00078fc000

def z472 : W := mkw 0x0186492286248841 0x000c324914312442 0x238e61838e260c76 0xc91c730c1c713063

def z473 : W := mkw 0xb670b68559cb34b8 0x85b385b42ace59a5 0x5c71860c71d83181 0x22e38c30638ec18c

def z474 : W := mkw 0x7ffdffef008a00a0 0x93ffefff78045005 0x7fffffff003e03ef 0xd3fffffff801f01f

def z475 : W := mkw 0x01064000edbe0000 0x08083200076df000 0x238e6000fffe0016 0xe91c730007fff000

def z476 : W := mkw 0x0410168010413410 0x002080b4008209a0 0xdc701f80f1c1fc1b 0xeee380fc078e0fe0

def z477 : W := mkw 0x0184492206048841 0x000c224910302442 0xa38061830e260e7e 0x5d1c030c18713073

def z478 : W := mkw 0x5a79a28569da14b0 0x8ad3cd142b4ed0a5 0xdc71e78f71fe3fff 0x7ee38f3c7b8ff1ff

def z479 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fffffff01c60c6f 0xdbfffffff80e3063

def z480 : W := mkw 0xfffdffef4b409c18 0x17ffefff7a5a04e0 0x7fffffff0fc00c0f 0xdbfffffff87e0060

def z481 : W := mkw 0x7fffffff84244245 0x13fffffffc212212 0x7fffffff0026026f 0xd3fffffff8013013

def z482 : W := mkw 0xa4901fef1241bc18 0x152480ff78920de0 0x80001fff0001fc08 0x140000fff8000fe0

def z483 : W := mkw 0x5b4f4000ed340000 0x0ada7a000769a000 0x7f8e6000fe260016 0xcbfc730007f13000

def z484 : W := mkw 0x73f4eba74d8e0000 0x1b9fa75d3a6c7000 0x23f061830fc60002 0x091f830c187e3000

def z485 : W := mkw 0x0c0b1400b0312000 0x006058a005818900 0xdc0f9e00f039f01d 0xe6e07cf00781cf80

def z486 : W := mkw 0x0080090002008800 0x0004004800100440 0x238018008e01c000 0x811c00c004700e00

def z487 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xff801f80fe01fc08 0x87fc00fc07f00fe0

def z488 : W := mkw 0x3ed91fc800000000 0x01f6c8fe40000000 0x7fff9ffc0000000f 0xd3fffcffe0000000

def z489 : W := mkw 0x0c0b1448a0300000 0x006058a245018000 0x5c0f9e7cf038001d 0xf2e07cf3e781c000

def z490 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e79f38e01c00e 0xd11c73cf9c700e00

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000260e70 0x0c00000000013073

def z492 : W := mkw 0x0032a29580ea56b4 0x80019514ac0752b5 0x807fffff81ffffff 0xfc03fffffc0fffff

def z493 : W := mkw 0xffffffd8ffffff1e 0x0ffffffec7fffff8 0xfffffffcffffff9f 0xffffffffe7fffffc

def z494 : W := mkw 0x0002001080204204 0x0000100084010210 0x800e79f38027ce7e 0xdc0073cf9c013e73

def z495 : W := mkw 0x5b6fe000a0300000 0x02db7f0005018000 0x7fffe000f0380017 0xe3ffff000781c000

def z496 : W := mkw 0x7bffeba7edbe0000 0x1bdfff5d3f6df000 0x7fffe183fffe0017 0xebffff0c1ffff000

def z497 : W := mkw 0x0184492202008800 0x000c224910100440 0xa38e79f38e01cc1e 0xdd1c73cf9c700e60

def z498 : W := mkw 0x5b6de00049000000 0x02db6f0002480000 0x7fffe000ffc00017 0xebffff0007fe0000

def z499 : W := mkw 0x5e69b448799b2102 0x0af34da243ccd908 0x5c71860c71d83181 0x22e38c30638ec18c

def z500 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff00260e7f 0xdffffffff8013073

def z501 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fff9e7c00000001 0x83fffcf3e0000000

def z502 : W := mkw 0x7fffffffefbeca45 0x1bffffffff7df652 0xffffffffffffce7f 0xfffffffffffffe73

def z503 : W := mkw 0x0c39b6cd00ca14b0 0x8061cdb6680650a5 0xdc7fffff01fe3fff 0xfee3fffff80ff1ff

def z504 : W := mkw 0x01964bb78664def5 0x800cb25dbc3326f7 0xa38e7fff8e27fffe 0xdd1c73fffc713fff

def z505 : W := mkw 0xfffdffef5b01a808 0x17ffefff7ad80d40 0x7ffffffffe01c00f 0xd3fffffffff00e00

def z506 : W := mkw 0x4124e000048e0000 0x0a09270000247000 0x0000600000060000 0x0000030000003000

def z507 : W := mkw 0x7ef9bfcd00000000 0x13f7cdfe68000000 0x7ff19f8c0000000b 0xc3ff8cfc60000000

def z508 : W := mkw 0x0400145810016306 0x002000a2c0800b18 0x80019e7c0039f39d 0x74000cf3e001cf9c

def z509 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e18708e27ce70 0x8d1c70c384713e73

def z510 : W := mkw 0x4829a000209a0000 0x0a414d000104d000 0x0001800000180000 0x00000c000000c000

def z511 : W := mkw 0x5f6ff448fdbf2102 0x0afb7fa247edf908 0x7fffe60cfffe3197 0xebffff3067fff18c

def z512 : W := mkw 0xb670b68559cb34b8 0x85b385b42ace59a5 0xdc71e78f71fe3fff 0x7ee38f3c7b8ff1ff

def z513 : W := mkw 0x5a79a28569da14b0 0x8ad3cd142b4ed0a5 0x5c71860c71d83181 0x22e38c30638ec18c

def z514 : W := mkw 0x0c09144830112102 0x006048a241808908 0xdc01860c7038339d 0x76e00c306381c19c

def z515 : W := mkw 0x5b4f4000edbe0000 0x0ada7a00076df000 0x7f8e0000fffe0010 0xabfc700007fff000

def z516 : W := mkw 0x0106403284244245 0x0008320194212212 0x238e60738e260276 0xd91c73039c713013

def z517 : W := mkw 0xf7f4ff805fcfbc18 0x0fbfa7fc02fe7de0 0xfff07f80ffc7fc1b 0xefff83fc07fe3fe0

def z518 : W := mkw 0x5f6ff458b0316306 0x02fb7fa2c5818b18 0xfffffe7cf039f39f 0xf7fffff3e781cf9c

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000600300260264 0x1000030018013013

def z520 : W := mkw 0x5b6fe00084240000 0x02db7f0004212000 0x7fffe0008e260017 0xcbffff0004713000

def z521 : W := mkw 0x1260a000498a0000 0x00930500024c5000 0x7ff1e000fffe0017 0xebff8f0007fff000

def z522 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071e78f01de3de3 0x28038f3c780ef1ef

def z523 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071e18301fe0c77 0x68038f0c180ff063

def z524 : W := mkw 0x5b7de28500ca14b0 0x82dbef14280650a5 0xffffe78f01fe3fff 0xffffff3c780ff1ff

def z525 : W := mkw 0x080b0000edbe0000 0x08405800076df000 0x5c0f8000fffe0015 0xeae07c0007fff000

def z526 : W := mkw 0x0080090002008800 0x0004004800100440 0x238001800e000c02 0x091c000c00700060

def z527 : W := mkw 0x00000000008a0000 0x0000000000045000 0x0000000001fe0010 0x28000000000ff000

def z528 : W := mkw 0x00000005000000a0 0x8000000028000005 0x0000000f000003e0 0x100000007800001f

def z529 : W := mkw 0x01b6ebb78624ca45 0x000db75dbc312652 0xa3ffffff8e27ce7f 0xdd1ffffffc713e73

def z530 : W := mkw 0x0c2bb458b0bb6306 0x00615da2c585db18 0xdc7ffe7cf1fff39f 0xfee3fff3e78fff9c

def z531 : W := mkw 0x0186493284244245 0x000c324994212212 0x238e79f30026026e 0xd11c73cf98013013

def z532 : W := mkw 0xfef9bfcd5b41bc18 0x17f7cdfe6ada0de0 0xfff19f8cffc1fc1b 0xefff8cfc67fe0fe0

def z533 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e19f08e01cc1a 0xcd1c70cf84700e60

def z534 : W := mkw 0x00000000004014b0 0x80000000000200a5 0x8000000000003fe0 0x04000000000001ff

def z535 : W := mkw 0xb2d00b804b409c18 0x0596805c025a04e0 0x7ff00180ffc00c13 0xebff800c07fe0060

def z536 : W := mkw 0x0c2bb45db0bb63a6 0x80615da2ed85db1d 0xdc0ffe7ff03ff3fd 0xf6e07ff3ff81ff9f

def z537 : W := mkw 0xa5965fb29665fe5d 0x052cb2fd94b32ff2 0xa38e7ff38e27fe7e 0xdd1c73ff9c713ff3

def z538 : W := mkw 0xb6f0bf805bcbbc18 0x05b785fc02de5de0 0xfff1ff80fffffc1f 0xefff8ffc07ffffe0

def z539 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8070678301c63c7b 0x6c03833c180e31e3

def z540 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8070618301fe3ff2 0x2c03830c180ff1ff

def z541 : W := mkw 0x0010028500ca14b0 0x80008014280650a5 0x8000078f01fe3ff8 0x3c00003c780ff1ff

def z542 : W := mkw 0x0030a28500000000 0x0001851428000000 0x0071860c00000001 0x00038c3060000000

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000600000260016 0x4800030000013000

def z544 : W := mkw 0x00b0ab8502ca9cb0 0x8005855c281654e5 0xa3f1ff8f8fffffff 0xfd1f8ffc7c7fffff

def z545 : W := mkw 0x0c0b1458b0fb77b6 0x806058a2c587dbbd 0xdc0f9e7cf1fffffd 0xfee07cf3e78fffff

def z546 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0xdc001f80f001fc19 0xe6e000fc07800fe0

def z547 : W := mkw 0x1240000049000000 0x0092000002480000 0x23f000000fc00002 0x091f8000007e0000

def z548 : W := mkw 0x080b0000a0300000 0x0040580005018000 0x5c0e0000f0000000 0x82e0700007800000

def z549 : W := mkw 0x7e79b6cd00000000 0x13f3cdb668000000 0x5c71e78f0000000f 0x52e38f3c78000000

def z550 : W := mkw 0x0d8f5d7ab0316306 0x006c7aebd5818b18 0xff8ffffff039f39f 0xf7fc7fffff81cf9c

def z551 : W := mkw 0x5feffd7affbfeb47 0x0aff7febd7fdff5a 0xffffffffffffffff 0xffffffffffffffff

def z552 : W := mkw 0x008009320200ca45 0x0004004990100652 0xa38019f38e01ce7a 0xdd1c00cf9c700e73

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x000061830000000e 0x5000030c18000000

def z554 : W := mkw 0x25945fef00000000 0x112ca2ff78000000 0x238e7fff0000000e 0xd11c73fff8000000

def z555 : W := mkw 0x0080090000000000 0x0004004800000000 0x238019800000000a 0xc11c00cc00000000

def z556 : W := mkw 0x0809000000000000 0x0040480000000000 0x5c0f800000000005 0xc2e07c0000000000

def z557 : W := mkw 0xffcd5d6a5b01a808 0x17fe6aeb52d80d40 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z558 : W := mkw 0x7e7bb6ddb0316306 0x13f3ddb6ed818b18 0xdc7f9e7cf039f39d 0xf6e3fcf3e781cf9c

def z559 : W := mkw 0xac9b1fd8b271ff1e 0x0564d8fec5938ff8 0xdc0f9ffcf039ff9d 0xf6e07cffe781cffc

def z560 : W := mkw 0x04801d7a1201eb47 0x002400ebd0900f5a 0x80001fff0001ffe8 0x140000fff8000fff

def z561 : W := mkw 0x0030a285008a00a0 0x8001851428045005 0x0071e78f003e03ef 0x50038f3c7801f01f

def z562 : W := mkw 0x00100285004014b0 0x80008014280200a5 0x8000678f00263ffe 0x5c00033c780131ff

def z563 : W := mkw 0x73f4eba700000000 0x139fa75d38000000 0x23fe79f30000000e 0xd11ff3cf98000000

def z564 : W := mkw 0x0c8b1d58b231eb06 0x006458eac5918f58 0xff8f9ffcfe39ff9f 0xfffc7cffe7f1cffc

def z565 : W := mkw 0x36f0bf8500ca14b0 0x81b785fc280650a5 0xfff1ff8f01fe3fff 0xffff8ffc780ff1ff

def z566 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0e1e70f001f019 0xe6e070f387800f80

def z567 : W := mkw 0x0020a000008a0000 0x0001050000045000 0x8071e18301fe0e7f 0x7c038f0c180ff073

def z568 : W := mkw 0x05865d7a9625eb47 0x002c32ebd4b12f5a 0xa38e7fff8e27fffe 0xdd1c73fffc713fff

def z569 : W := mkw 0x5b4f4000ed340000 0x0ada7a000769a000 0x7f8f8000fe380015 0xe3fc7c0007f1c000

def z570 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xa3f01f800fc1fc0a 0x0d1f80fc007e0fe0

def z571 : W := mkw 0x7ffdffff0200ca45 0x13ffeffff8100652 0xffffffff0001ce6f 0xd7fffffff8000e73

def z572 : W := mkw 0x010640108624ca45 0x0008320084312652 0xa38e60008e27ce76 0xcd1c730004713e73

def z573 : W := mkw 0x241016cd00000000 0x112080b668000000 0x0000060c00000000 0x0000003060000000

def z574 : W := mkw 0x73f4eba700ca14b0 0x939fa75d380650a5 0xa3f1e78f01fe3fff 0x7d1f8f3c780ff1ff

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001860c00183181 0x20000c306000c18c

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001800000380015 0x60000c000001c000

def z577 : W := mkw 0x008209328624ca45 0x0004104994312652 0x800019f38e27ce78 0x1c0000cf9c713e73

def z578 : W := mkw 0x32d00b8000000000 0x0196805c00000000 0x23f0018000000002 0x011f800c00000000

def z579 : W := mkw 0xb6d21f80ffffbc18 0x0db690fc07fffde0 0xfff01f80fffffc1b 0xefff80fc07ffffe0

def z580 : W := mkw 0xb250028049401418 0x05928014024a00a0 0x0070000001c00000 0x00038000000e0000

def z581 : W := mkw 0xffdd5fea5b41bc18 0x17feeaff52da0de0 0xfffe1ff0ffc1fc1b 0xeffff0ff87fe0fe0

def z582 : W := mkw 0x0d0f547ab4356347 0x00687aa3d5a1ab1a 0xdc0ffe7ff03ff3fd 0xf6e07ff3ff81ff9f

def z583 : W := mkw 0x5366e000cdae0000 0x0a9b3700066d7000 0x23fe60008fe60016 0xc91ff300047f3000

def z584 : W := mkw 0x0c8b1d7ab231eb47 0x006458ebd5918f5a 0xdc0f9ffff039fffd 0xf6e07cffff81cfff

def z585 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071e60f01fe33e5 0x30038f30780ff19f

def z586 : W := mkw 0x0c3bb6ddb0316306 0x0061ddb6ed818b18 0xdc7ffffff039f39f 0xf6e3ffffff81cf9c

def z587 : W := mkw 0x0020a005008a00a0 0x8001050028045005 0x0001800c00180180 0x00000c006000c00c

def z588 : W := mkw 0x0400144810012102 0x002000a240800908 0x0000060c00003180 0x000000306000018c

def z589 : W := mkw 0x00100285004014b0 0x80008014280200a5 0x8001878f00383ffd 0x74000c3c7801c1ff

def z590 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8001e78f003e3fec 0x14000f3c7801f1ff

def z591 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800e18708e27ce7c 0xdc0070c384713e73

def z592 : W := mkw 0x492fe07f84244245 0x12497f03fc212212 0x000fe07f00260264 0x10007f03f8013013

def z593 : W := mkw 0x49afe932a6beca45 0x0a4d7f499535f652 0xa38ff9f38e3fce7e 0xdd1c7fcf9c71fe73

def z594 : W := mkw 0x24901fff10016306 0x112480fff8800b18 0x80001fff0001f388 0x140000fff8000f9c

def z595 : W := mkw 0x0080092202008841 0x0004004910100442 0x0000018300000c60 0x0000000c18000063

def z596 : W := mkw 0x0809004820100102 0x0040480241008008 0x0001800c00180180 0x00000c006000c00c

def z597 : W := mkw 0x7fffffef84240000 0x13ffffff7c212000 0x7fffffff8e26001f 0xdbfffffffc713000

def z598 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0e1e7cf001f388 0x96e070f3e7800f9c

def z599 : W := mkw 0x8000000059413418 0x0400000002ca09a0 0x0000000071c03000 0x20000000038e0180

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x0070000001c00013 0x68038000000e0000

def z601 : W := mkw 0x0c09145810016306 0x006048a2c0800b18 0xdc0f9e7c0001f38d 0xd6e07cf3e0000f9c

def z602 : W := mkw 0x0c0b1458fdbf6306 0x086058a2c7edfb18 0xdc0f9e7cfffff39d 0xfee07cf3e7ffff9c

def z603 : W := mkw 0x0c1b16ddb07177b6 0x8060d8b6ed838bbd 0xdc0f9ffff039fffd 0xf6e07cffff81cfff

def z604 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c01860c00000001 0x02e00c3060000000

def z605 : W := mkw 0x008009320200ca45 0x0004004990100652 0x800079f30027ce7e 0x5c0003cf98013e73

def z606 : W := mkw 0x73f4eba706048841 0x139fa75d38302442 0x23f061830e060c62 0x091f830c18703063

def z607 : W := mkw 0x0400140010012000 0x002000a000800900 0xdc019e0cf039f39d 0xf6e00cf06781cf9c

def z608 : W := mkw 0x0104400004040000 0x0008220000202000 0x238060000e060002 0x091c030000703000

def z609 : W := mkw 0x493fe285a4fe14b0 0x8a49ff142d27f0a5 0x807fe78f01fe3fff 0x7c03ff3c780ff1ff

def z610 : W := mkw 0x0002001080204204 0x0000100084010210 0x800f9e7c8039f39d 0xf4007cf3e401cf9c

def z611 : W := mkw 0xb6c01d005b01a808 0x05b600e802d80d40 0xff801e00fe01f019 0xe7fc00f007f00f80

def z612 : W := mkw 0x0002001080204204 0x0000100084010210 0x000e007000200204 0x1000700380010010

def z613 : W := mkw 0x080b0010b0316306 0x0040580085818b18 0xdc0f8000f039f395 0xe6e07c000781cf9c

def z614 : W := mkw 0x0c39b6cd30db35b2 0x8061cdb66986d9ad 0x5c71860c71d83181 0x22e38c30638ec18c

def z615 : W := mkw 0x00100285004014b0 0x80008014280200a5 0x0000018300000c60 0x0000000c18000063

def z616 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071e60c01fe3197 0x68038f30600ff18c

def z617 : W := mkw 0x800000004b409c18 0x04000000025a04e0 0x000000000fc00c00 0x08000000007e0060

def z618 : W := mkw 0x0184492206048841 0x000c224910302442 0x238000000e000000 0x011c000000700000

def z619 : W := mkw 0x7fffffff80204204 0x13fffffffc010210 0xffffffff8021c21f 0xd7fffffffc010e10

def z620 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071e18f01fe0fe6 0x18038f0c780ff07f

def z621 : W := mkw 0xb640140059012008 0x05b200a002c80900 0x5c00000070000000 0x02e0000003800000

def z622 : W := mkw 0x0106403284244245 0x0008320194212212 0x000e007000000000 0x0000700380000000

def z623 : W := mkw 0x0430b6dd10cb77b6 0x802185b6e8865bbd 0x8071ffff01ffffff 0x7c038ffff80fffff

def z624 : W := mkw 0x5374e2854dce14b0 0x8a9ba7142a6e70a5 0xa3f1e78f0ffe3fff 0x7d1f8f3c787ff1ff

def z625 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0f9e7cf001c00d 0xd2e07cf3e7800e00

def z626 : W := mkw 0x7fffffffb635eb47 0x13fffffffdb1af5a 0xfffffffffe3fffff 0xfffffffffff1ffff

def z627 : W := mkw 0x04801d001201a800 0x002400e800900d40 0xff801f80fe01fc1b 0xeffc00fc07f00fe0

def z628 : W := mkw 0x80020000ffffbc18 0x0c00100007fffde0 0x80000000fffffc10 0x2c00000007ffffe0

def z629 : W := mkw 0x0136e2b784ee56f5 0x8009b715bc2772b7 0x807fe7ff01fe3fff 0x7c03ff3ff80ff1ff

def z630 : W := mkw 0x492fe07fa0304306 0x12497f03fd018218 0x000fe07f00380384 0x10007f03f801c01c

def z631 : W := mkw 0x1250028049401410 0x00928014024a00a0 0xfff00780ffc03c1b 0xefff803c07fe01e0

def z632 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e78708e27c016 0xc91c73c384713e00

def z633 : W := mkw 0x0d0f5458b4356306 0x00687aa2c5a1ab18 0xff8ffe7cfe3ff39f 0xfffc7ff3e7f1ff9c

def z634 : W := mkw 0x5a49000069100000 0x0ad2480003488000 0x5c00000070000000 0x02e0000003800000

def z635 : W := mkw 0xb7c65d32df25ea4d 0x05be32e996f92f52 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z636 : W := mkw 0x20900ba700000000 0x1104805d38000000 0x0000018300000000 0x0000000c18000000

def z637 : W := mkw 0x5a6ba000edbe0000 0x0ad35d00076df000 0x5c718000fffe0011 0x2ae38c0007fff000

def z638 : W := mkw 0xfef9bf807bdbbc18 0x0ff7cdfc03dedde0 0xfff19f80ffd9fc1b 0xefff8cfc07fecfe0

def z639 : W := mkw 0x018449320604ca45 0x000c224990302652 0xa38079f30e07ce6a 0x1d1c03cf98703e73

def z640 : W := mkw 0x00100285004014b0 0x80008014280200a5 0x8070078f01c03ffb 0x7c03803c780e01ff

def z641 : W := mkw 0x080b0058a0304306 0x00405802c5018218 0x800f867c0038339d 0x74007c33e001c19c

def z642 : W := mkw 0x098f497aa634cb47 0x004c7a4bd531a65a 0xa38ff9ff8e3fcffe 0xdd1c7fcffc71fe7f

def z643 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80701f8001c1fc1b 0x6c0380fc000e0fe0

def z644 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ff1e78f00000003 0x03ff8f3c78000000

def z645 : W := mkw 0xb650168059413418 0x05b280b402ca09a0 0x7ff00600ffc03013 0xebff803007fe0180

def z646 : W := mkw 0xb6f0bf855b41bc18 0x05b785fc2ada0de0 0xfff1ff8fffc1fc1f 0xffff8ffc7ffe0fe0

def z647 : W := mkw 0x0c39b6cd30db35b2 0x8061cdb66986d9ad 0xdc71e78f71fe3fff 0x7ee38f3c7b8ff1ff

def z648 : W := mkw 0x0020a000008a0000 0x0001050000045000 0x0001e000003e0004 0x00000f000001f000

def z649 : W := mkw 0xbed91fc87b51bd1a 0x05f6c8fe43da8de8 0xfff19f8cffd9fd9b 0xefff8cfc67fecfec

def z650 : W := mkw 0xb7f6ffb7dfeffefd 0x85bfb7fdbeff7ff7 0xffffffffffffffff 0xffffffffffffffff

def z651 : W := mkw 0x7ffffffffdbf6306 0x1bffffffffedfb18 0xfffffffffffff39f 0xffffffffffffff9c

def z652 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x800e1870f039f39c 0xf40070c38781cf9c

def z653 : W := mkw 0x7fffffefed340000 0x1bffffff7f69a000 0x7ffffffffe00000f 0xd3fffffffff00000

def z654 : W := mkw 0x5bcf4932ef34ca45 0x0ade7a499779a652 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z655 : W := mkw 0xb7d65fb2df65fe5d 0x05beb2fd96fb2ff2 0xfffe1ff0ffc1fc1b 0xeffff0ff87fe0fe0

def z656 : W := mkw 0x80020010fb71ff1e 0x0400100087db8ff8 0x80000000fff9ff90 0x2c00000007ffcffc

def z657 : W := mkw 0x0c1b16d8b0717716 0x0060d8b6c5838bb8 0xdc7f9ffcf1f9ff9f 0xfee3fcffe78fcffc

def z658 : W := mkw 0x5f4f5458fd356306 0x0afa7aa2c7e9ab18 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000060000003019 0x6400003000000180

def z660 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0xa3801f808e01fc1a 0xcd1c00fc04700fe0

def z661 : W := mkw 0x3650168000000000 0x01b280b400000000 0x5c70060000000001 0x02e3803000000000

def z662 : W := mkw 0x5b7fe285edfe14b0 0x8adbff142f6ff0a5 0x7fffe183fffe0c77 0xebffff0c1ffff063

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000018300000e68 0x1400000c18000073

def z664 : W := mkw 0x0020a000008a0000 0x0001050000045000 0x8071e60c01fe339f 0x7c038f30600ff19c

def z665 : W := mkw 0x0184492206048841 0x000c224910302442 0xa38079838e07cc7a 0xcd1c03cc1c703e63

def z666 : W := mkw 0x5a69a00000000000 0x02d34d0000000000 0x5c71800000000001 0x02e38c0000000000

def z667 : W := mkw 0xb650168059413418 0x05b280b402ca09a0 0xdc70078071c03c1b 0x6ee3803c038e01e0

def z668 : W := mkw 0x7ffdff8000000000 0x03ffeffc00000000 0x7fffff800000000f 0xc3fffffc00000000

def z669 : W := mkw 0xb6d01f805bcbbcb8 0x85b680fc02de5de5 0xfff01f80fffffffb 0xefff80fc07ffffff

def z670 : W := mkw 0xfe79b68079db3418 0x0ff3cdb403ced9a0 0x5c71860071d83001 0x22e38c30038ec180

def z671 : W := mkw 0x5260a000498a0000 0x0a930500024c5000 0x0070000001c00000 0x00038000000e0000

def z672 : W := mkw 0x7fffffefa0300000 0x13ffffff7d018000 0x7ffffffff038001f 0xf3ffffffff81c000

def z673 : W := mkw 0x24b0bfef00000000 0x112585ff78000000 0x0071ffff0000000f 0x50038ffff8000000

def z674 : W := mkw 0xb2f0ab854bca9cb8 0x8597855c2a5e54e5 0x23f061830fc60c62 0x091f830c187e3063

def z675 : W := mkw 0x5befe900efbe8800 0x0adf7f48077df440 0xfffff980ffffcc1f 0xefffffcc07fffe60

def z676 : W := mkw 0x7fffffff8624ca45 0x13fffffffc312652 0x7fffffff8e01c00f 0xd3fffffffc700e00

def z677 : W := mkw 0x53e4e9224f8e8841 0x0a9f2749127c7442 0x23f061830fc60c62 0x091f830c187e3063

def z678 : W := mkw 0x0106400084240000 0x0008320004212000 0xa38e61838e260e7e 0xdd1c730c1c713073

def z679 : W := mkw 0x01864932efbeca45 0x080c3249977df652 0xa38e79f3ffffce7e 0xfd1c73cf9ffffe73

def z680 : W := mkw 0x5befe932efbeca45 0x0adf7f49977df652 0x7ffff870ffffc017 0xebffffc387fffe00

def z681 : W := mkw 0x008209108220ca04 0x0004104884110650 0xa38e19f08e21ce1e 0xdd1c70cf84710e70

def z682 : W := mkw 0x7fcf5d6aed340000 0x1bfe7aeb5769a000 0x7f8e1870fe000000 0x83fc70c387f00000

def z683 : W := mkw 0x8030a2855bcbbcb8 0x840185142ade5de5 0x8071e78fffffffff 0x7c038f3c7fffffff

def z684 : W := mkw 0x0020a000008a0000 0x0001050000045000 0x0070600001c60002 0x08038300000e3000

def z685 : W := mkw 0x00000000699a0000 0x08000000034cd000 0x0000000071d80000 0x20000000038ec000

def z686 : W := mkw 0x5f6ff458fdbf6306 0x0afb7fa2c7edfb18 0x7ffff870ffffc017 0xebffffc387fffe00

def z687 : W := mkw 0x0010028000401410 0x00008014000200a0 0x8070678301e63e7f 0x7c03833c180f31f3

def z688 : W := mkw 0x5b7de28500000000 0x02dbef1428000000 0x7fffe78f0000000f 0xd3ffff3c78000000

def z689 : W := mkw 0xffeffd00ffbfa808 0x0fff7fe807fdfd40 0x7ffff800ffffc017 0xebffffc007fffe00

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000018000000c1a 0x4c00000c00000060

def z691 : W := mkw 0x090f407aa4344347 0x00487a03d521a21a 0x000fe07f003e03e4 0x10007f03f801f01f

def z692 : W := mkw 0xfbffeb80effe9c18 0x0fdfff5c077ff4e0 0x7fffe180fffe0c17 0xebffff0c07fff060

def z693 : W := mkw 0x5364e00000000000 0x029b270000000000 0x23f0600000000002 0x011f830000000000

def z694 : W := mkw 0xbe5916c87951351a 0x05f2c8b643ca89a8 0x5c71860c71d83181 0x22e38c30638ec18c

def z695 : W := mkw 0x082ba05da0ba43a6 0x80415d02ed05d21d 0x000fe07f003e03e4 0x10007f03f801f01f

def z696 : W := mkw 0x0002001080204204 0x0000100084010210 0x000e18708001c000 0x800070c384000e00

def z697 : W := mkw 0x0c0b1448b0312102 0x006058a245818908 0x5c0f860cf0383195 0xe2e07c306781c18c

def z698 : W := mkw 0x77f4ffa700000000 0x13bfa7fd38000000 0x7ff07f830000000b 0xc3ff83fc18000000

def z699 : W := mkw 0x5e6bb458f9bb6306 0x0af35da2c7cddb18 0xdc7f9e7cf1f9f39d 0xf6e3fcf3e78fcf9c

def z700 : W := mkw 0x01b4eba706ce9cf1 0x800da75d383674e7 0x23f061830fc60c62 0x091f830c187e3063

def z701 : W := mkw 0x5374e2854dce14b0 0x8a9ba7142a6e70a5 0x23f061830fc60c62 0x091f830c187e3063

def z702 : W := mkw 0x5f6ff400fdbf2000 0x0afb7fa007edf900 0xfffffe00fffff01f 0xeffffff007ffff80

def z703 : W := mkw 0x01a6e93786aecae5 0x800d3749bc357657 0xa38ff9ff8e3fcffe 0xdd1c7fcffc71fe7f

def z704 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8070618301e60e7e 0x5c03830c180f3073

def z705 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8070678f01c63fea 0x1c03833c780e31ff

def z706 : W := mkw 0x0400145810016306 0x002000a2c0800b18 0xdc001e7cf001f399 0xf6e000f3e7800f9c

def z707 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff01f80ffc1f00b 0xe3ff80fc07fe0f80

def z708 : W := mkw 0xb2d00b804b409c18 0x0596805c025a04e0 0xfff01980ffc1cc1b 0xefff80cc07fe0e60

def z709 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800000000027ce60 0x0400000000013e73

def z710 : W := mkw 0x7fcd5d6a00ca14b0 0x93fe6aeb500650a5 0xff8e187001fe3ff0 0xaffc70c3800ff1ff

def z711 : W := mkw 0x5bede9224f8e8841 0x0adf6f49127c7442 0x7ffff9f30fc60c6f 0xdbffffcf987e3063

def z712 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800001838e27ce78 0x1c00000c1c713e73

def z713 : W := mkw 0x7ffdffef6d9e0000 0x1bffefff7b6cf000 0x7fffffff7fde000f 0xfbfffffffbfef000

def z714 : W := mkw 0x0002001086aecae5 0x8000100084357657 0x800000008e3fcff0 0x0c0000000471fe7f

def z715 : W := mkw 0x7ffdffef02409c10 0x13ffefff781204e0 0xffffffff8fc1fc1f 0xfffffffffc7e0fe0

def z716 : W := mkw 0x01a4e92700000000 0x000d274938000000 0x238ff9ff0000000e 0xd11c7fcff8000000

def z717 : W := mkw 0x37c45d2200000000 0x01be22e910000000 0x7f8e187000000000 0x83fc70c380000000

def z718 : W := mkw 0x5b6de0006d9e0000 0x0adb6f00036cf000 0x7fffe0007fde0007 0xebffff0003fef000

def z719 : W := mkw 0x7bcd496a00000000 0x13de6a4b50000000 0x238e007000000000 0x011c700380000000

def z720 : W := mkw 0xb6c21d10df25ea4d 0x05b610e886f92f52 0xff801800fe27ce70 0x8ffc00c007f13e73

def z721 : W := mkw 0xbe5b16d8fb71ff1e 0x05f2d8b6c7db8ff8 0xdc71860cfff9ff91 0x2ee38c3067ffcffc

def z722 : W := mkw 0x0184492206048841 0x000c224910302442 0xa38e79f38e07cc7e 0xdd1c73cf9c703e63

def z723 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e787300000004 0x93fc73c398000000

def z724 : W := mkw 0x7fdd5fef00000000 0x13feeaff78000000 0x7f8f9fff0000000d 0xd3fc7cfff8000000

def z725 : W := mkw 0x1240000049000000 0x0092000002480000 0xfff01800ffc1c01b 0xefff80c007fe0e00

def z726 : W := mkw 0x5b6fe010edbe4204 0x0adb7f00876df210 0x7fffe070fffe0217 0xfbffff0387fff010

def z727 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0xff8f9e7c0038339d 0xf7fc7cf3e001c19c

def z728 : W := mkw 0x5b6fe000edbe00a0 0x8adb7f00076df005 0x7fffe000fffe03f7 0xebffff0007fff01f

def z729 : W := mkw 0xfffdffef1241bcb8 0x97ffefff78920de5 0xffffffff0001ffef 0xd7fffffff8000fff

def z730 : W := mkw 0x0c0b1458b4356347 0x006058a2c5a1ab1a 0xdc0f9e7cf03ff3fd 0xf6e07cf3e781ff9f

def z731 : W := mkw 0x7fdd5fea00000000 0x13feeaff50000000 0x7ffe1e7000000001 0x83fff0f380000000

def z732 : W := mkw 0x0032a29586eedef5 0x80019514ac3776f7 0x807061838fe7ce72 0x0c03830c1c7f3e73

def z733 : W := mkw 0x1240000049000000 0x0092000002480000 0x7ff06000ffe60017 0xebff830007ff3000

def z734 : W := mkw 0x6dadfd6f00000000 0x136d6feb78000000 0x000ff87f00000004 0x10007fc3f8000000

def z735 : W := mkw 0x092fe07fa4be43e7 0x80497f03fd25f21f 0x000fe07f003e03e4 0x10007f03f801f01f

def z736 : W := mkw 0x01864932a634cb47 0x000c32499531a65a 0xa38e79f38e3fcffe 0xdd1c73cf9c71fe7f

def z737 : W := mkw 0x00020010f9316306 0x0000100087c98b18 0x80000000fff9f390 0x2c00000007ffcf9c

def z738 : W := mkw 0x01b6ebb786eedef5 0x800db75dbc3776f7 0x23ff9e7c8fd9f181 0xa11ffcf3e47ecf8c

def z739 : W := mkw 0x16421410fdbf6306 0x08b210a087edfb18 0xfff01e00fffff39b 0xefff80f007ffff9c

def z740 : W := mkw 0xfffdffef4b409c18 0x17ffefff7a5a04e0 0xffffffff8fc1cc1f 0xdffffffffc7e0e60

def z741 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0ffe7ff03ff3fd 0xf6e07ff3ff81ff9f

def z742 : W := mkw 0x0c3bb6ddb0fb77b6 0x8061ddb6ed87dbbd 0x5c7e79f3f1c7cc62 0x8ae3f3cf9f8e3e63

def z743 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0xffffffff003e3fef 0xd7fffffff801f1ff

def z744 : W := mkw 0xc92de06f5b41bc18 0x16496f037ada0de0 0x800fe07fffc1fc14 0x3c007f03fffe0fe0

def z745 : W := mkw 0x7f7df6ef00ca14b0 0x93fbefb7780650a5 0x5c7fe67f01fe33e5 0x32e3ff33f80ff19f

def z746 : W := mkw 0x2c891d6a00000000 0x116448eb50000000 0x5c0e187000000000 0x82e070c380000000

def z747 : W := mkw 0x0002001084244245 0x0000100084212212 0x000000008e260270 0x0800000004713013

def z748 : W := mkw 0x7ffdffef30112102 0x13ffefff79808908 0xfffffffff019f19f 0xf7ffffffff80cf8c

def z749 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f9e7c0018318d 0xf2e07cf3e000c18c

def z750 : W := mkw 0x80020010fb71ff1e 0x0400100087db8ff8 0x80000000ffc1fc10 0x2c00000007fe0fe0

def z751 : W := mkw 0x01a4e92200000000 0x000d274910000000 0x23fff9f30000000f 0xd11fffcf98000000

def z752 : W := mkw 0x12420000ed340000 0x089210000769a000 0x7ff00000ffc00013 0xebff800007fe0000

def z753 : W := mkw 0x12c20910efbeca45 0x08961048877df652 0xfff01980ffffce7b 0xefff80cc07fffe73

def z754 : W := mkw 0x7e7bb6dd8624ca45 0x13f3ddb6ec312652 0xdc71860c8e27ce71 0x0ee38c3064713e73

def z755 : W := mkw 0xb2d20b90fb71ff1e 0x0596905c87db8ff8 0xa3f00180fff9ff92 0x2d1f800c07ffcffc

def z756 : W := mkw 0x5b6fe005edbe00a0 0x8adb7f002f6df005 0xffffe60ffffe33ff 0xffffff307ffff19f

def z757 : W := mkw 0x49ade96f06048841 0x124d6f4b78302442 0x238fe1ff0e060c66 0x191c7f0ff8703063

def z758 : W := mkw 0x0c09144830112102 0x006048a241808908 0xdc0f9e7cf019f19d 0xf6e07cf3e780cf8c

def z759 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7ffe6000ffc60013 0xebfff30007fe3000

def z760 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x00000000f039c380 0x000000000781ce1c

def z761 : W := mkw 0x0124e027008a00a0 0x8009270138045005 0x000fe07f003e03e4 0x10007f03f801f01f

def z762 : W := mkw 0x5f7df6cd00ca14b0 0x82fbefb6680650a5 0xffffffff01fe3fff 0xfffffffff80ff1ff

def z763 : W := mkw 0xbed91fc85b41bc18 0x05f6c8fe42da0de0 0xffff9ffcfff9ff9f 0xfffffcffe7ffcffc

def z764 : W := mkw 0xfbfdebef4b409c18 0x17dfef5f7a5a04e0 0x23ffe1ff0fc00c06 0x191fff0ff87e0060

def z765 : W := mkw 0x7fedfd6a00000000 0x13ff6feb50000000 0x7fff987000000001 0x83fffcc380000000

def z766 : W := mkw 0x1240000049000000 0x0092000002480000 0x7ff000007fc00003 0x2bff800003fe0000

def z767 : W := mkw 0xb6c21d10fb31eb0e 0x05b610e887d98f58 0x7f801800fe01c000 0x83fc00c007f00e00

def z768 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7ffe0000ffc00000 0x83fff00007fe0000

def z769 : W := mkw 0xb75656b2dd65765d 0x05bab2b596eb2bb2 0x5c7e667371e63265 0x32e3f3339b8f3193

def z770 : W := mkw 0x5fedfd6a00000000 0x02ff6feb50000000 0x7fffffff0000000f 0xd3fffffff8000000

def z771 : W := mkw 0x73f6ebb7b0316306 0x139fb75dbd818b18 0xa3f06183f039f392 0x251f830c1f81cf9c

def z772 : W := mkw 0x00020010b0bb63a6 0x800010008585db1d 0x80000000f03ff3f0 0x240000000781ff9f

def z773 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfffe1ff0ffc1fc1f 0xfffff0ff87fe0fe0

def z774 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0ffffff039f39f 0xf6e07fffff81cf9c

def z775 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x800000000039f380 0x040000000001cf9c

def z776 : W := mkw 0x5b6de0004d8e0000 0x0adb6f00026c7000 0x7fffe000ffc60017 0xebffff0007fe3000

def z777 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01f80ffe7fe7b 0xefff80fc07ff3ff3

def z778 : W := mkw 0x5b6fe07fedbe4306 0x1adb7f03ff6df218 0x7fffe07ffffe0397 0xfbffff03fffff01c

def z779 : W := mkw 0x7ffdffef4dce14b0 0x9bffefff7a6e70a5 0xffffffff0ffe3fff 0xfffffffff87ff1ff

def z780 : W := mkw 0x3ec91d4800000000 0x01f648ea40000000 0x7f8f9e7c0000000d 0xd3fc7cf3e0000000

def z781 : W := mkw 0x0c891d4802008800 0x006448ea40100440 0xff8f9ffc8e01cc1f 0xdffc7cffe4700e60

def z782 : W := mkw 0x7ffdffef06ce9cf1 0x93ffefff783674e7 0x7fffffff0fc60c6f 0xdbfffffff87e3063

def z783 : W := mkw 0x1640140059012000 0x00b200a002c80900 0x7ff01800ffc1c013 0xebff80c007fe0e00

def z784 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x8001860cf039f391 0x24000c306781cf9c

def z785 : W := mkw 0x73c4492200000000 0x139e224910000000 0x238e79f30000000e 0xd11c73cf98000000

def z786 : W := mkw 0x818449225b41bc18 0x040c224912da0de0 0xa38e79f3ffc1fc1e 0xfd1c73cf9ffe0fe0

def z787 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xff8f9e7cfe39f39f 0xfffc7cf3e7f1cf9c

def z788 : W := mkw 0xb6e0bd055b8ba8a8 0x85b705e82adc5d45 0x7f81f80ffe3fc3e4 0x93fc0fc07ff1fe1f

def z789 : W := mkw 0xedbdffef1241bc18 0x176defff78920de0 0x800fffff0001fc0c 0x14007ffff8000fe0

def z790 : W := mkw 0x001202958664def5 0x80009014ac3326f7 0x8000078f8e27fff8 0x1c00003c7c713fff

def z791 : W := mkw 0x5b6fe032edbe4245 0x0adb7f01976df212 0xfffff873ffffc27f 0xffffffc39ffffe13

def z792 : W := mkw 0x0184492202008800 0x000c224910100440 0xa38e79f30001cc0e 0xd51c73cf98000e60

def z793 : W := mkw 0xb6d01fc85b41bc18 0x05b680fe42da0de0 0xfff01ffcffc1fc1b 0xffff80ffe7fe0fe0

def z794 : W := mkw 0x0c09144800ca14b0 0x806048a2400650a5 0xdc0f9e7c01fe3ffd 0xfee07cf3e00ff1ff

def z795 : W := mkw 0xfffdffef59cb34b8 0x97ffefff7ace59a5 0x7fffffff71d8318f 0xf3fffffffb8ec18c

def z796 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e79f30026026e 0xd11c73cf98013013

def z797 : W := mkw 0x7ffdffef49401410 0x13ffefff7a4a00a0 0xffffffffffc03c1f 0xfffffffffffe01e0

def z798 : W := mkw 0x4d2df46f00000000 0x12696fa378000000 0x5c0fe67f00000005 0x12e07f33f8000000

def z799 : W := mkw 0x0184492200000000 0x000c224910000000 0xa38e79f38001c01e 0xd51c73cf9c000e00

def z800 : W := mkw 0x5b6fe000cd240000 0x02db7f0006692000 0x7fffe000ffe60017 0xebffff0007ff3000

def z801 : W := mkw 0xfffdffef1241bc18 0x17ffefff78920de0 0xfffffffff001fc1f 0xf7ffffffff800fe0

def z802 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x8000060cf039f398 0x340000306781cf9c

def z803 : W := mkw 0x05845d2210012000 0x002c22e910800900 0xff8e7ff3f001f01f 0xf7fc73ff9f800f80

def z804 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc019e0cf039f399 0xe6e00cf06781cf9c

def z805 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e19f00000000a 0xc3fc70cf80000000

def z806 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0e1e7000000009 0xc2e070f380000000

def z807 : W := mkw 0x7ffdffef10012000 0x13ffefff78800900 0x7fffffff7000300f 0xf3fffffffb800180

def z808 : W := mkw 0xac9b1fd8b271ff1e 0x0564d8fec5938ff8 0x800f9ffc0039ff8c 0x14007cffe001cffc

def z809 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0e18700000000c 0xd2e070c380000000

def z810 : W := mkw 0xbfdd5fea5b41bc18 0x05feeaff52da0de0 0xffffffffffc1fc1f 0xfffffffffffe0fe0

def z811 : W := mkw 0xfffdffef02409c18 0x17ffefff781204e0 0x7fffffff00000c0f 0xd3fffffff8000060

def z812 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f9e7cf000001d 0xf2e07cf3e7800000

def z813 : W := mkw 0x5764f4585d8f6306 0x0abb27a2c2ec7b18 0xa3f07e7c0fc7f38a 0x1d1f83f3e07e3f9c

def z814 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0x7ffe79f3ffc1cc02 0x8bfff3cf9ffe0e60

def z815 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c000000f001c000 0x02e0000007800e00

def z816 : W := mkw 0x5b6fe000ed340000 0x0adb7f000769a000 0x7fffe000ffc00017 0xebffff0007fe0000

def z817 : W := mkw 0xffdd5fea4b409c18 0x17feeaff525a04e0 0x7ffe19f00fc00c02 0x8bfff0cf807e0060

def z818 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff00000003 0x83fffffff8000000

def z819 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff00780ffc1fc13 0x2fff803c07fe0fe0

def z820 : W := mkw 0x00020010a6beca45 0x080010008535f652 0x800000008e3fce70 0x0c0000000471fe73

def z821 : W := mkw 0xf3f4eba74bca9cb8 0x979fa75d3a5e54e5 0x23f061830fc60c62 0x091f830c187e3063

def z822 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xffffe000fffe3397 0xefffff0007fff19c

def z823 : W := mkw 0x2c991fc800000000 0x0164c8fe40000000 0x5c0f9ffc0000000d 0xd2e07cffe0000000

def z824 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffffe7c00000007 0xc3fffff3e0000000

def z825 : W := mkw 0x000200108624ca45 0x0000100084312652 0x000000000e260e60 0x0800000000713073

def z826 : W := mkw 0xa4921f909665fe5d 0x052490fc84b32ff2 0x80001f808e27fe78 0x0c0000fc04713ff3

def z827 : W := mkw 0x124000004b008800 0x0092000002580440 0xfff00000ffc1cc13 0xefff800007fe0e60

def z828 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff01c0001f 0xfbfffffff80e0000

def z829 : W := mkw 0x7ffdffef02008800 0x13ffefff78100440 0x7fffffff0e000c0f 0xdbfffffff8700060

def z830 : W := mkw 0x5b6fe07fedbe4245 0x1adb7f03ff6df212 0x7fffe07ffffe0277 0xfbffff03fffff013

def z831 : W := mkw 0x5b6de06f49000000 0x12db6f037a480000 0x7fffe07fffc00017 0xfbffff03fffe0000

def z832 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38ff9f38e3fce7f 0xfd1c7fcf9c71fe73

def z833 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe183fffe001f 0xfbffff0c1ffff000

def z834 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe000ffc60007 0xcbffff0007fe3000

def z835 : W := mkw 0x0c39b6cd00ca14b0 0x8061cdb6680650a5 0x5c7fffff01c60c6f 0xdae3fffff80e3063

def z836 : W := mkw 0xa4901f851241bcb8 0x852480fc28920de5 0x80001f8c0001fd88 0x040000fc60000fec

def z837 : W := mkw 0x5b6fe010edbe4306 0x0adb7f00876df218 0x7fffe000fffe0397 0xebffff0007fff01c

def z838 : W := mkw 0xb6d21f90dfeffefd 0x85b690fc86ff7ff7 0xfff01f80fffffffb 0xefff80fc07ffffff

def z839 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff01980ffc1cc13 0xebff80cc07fe0e60

def z840 : W := mkw 0xffcd5d6a5b41bc18 0x17fe6aeb52da0de0 0xff8e1870ffc1fc10 0xaffc70c387fe0fe0

def z841 : W := mkw 0x080b0010b0316306 0x0040580085818b18 0xdc018000f039f391 0x26e00c000781cf9c

def z842 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x00001e000001f000 0x000000f000000f80

def z843 : W := mkw 0x008209108624ca45 0x0004104884312652 0x238018008e01c000 0x811c00c004700e00

def z844 : W := mkw 0x0c09144810012000 0x006048a240800900 0xdc0e1e70f001f019 0xe6e070f387800f80

def z845 : W := mkw 0x000200108624ca45 0x0000100084312652 0x000000008e07cc60 0x0800000004703e63

def z846 : W := mkw 0x7fcd5d6a02008800 0x13fe6aeb50100440 0xff8e19f08e01cc1a 0xcffc70cf84700e60

def z847 : W := mkw 0x0184492202008800 0x000c224910100440 0xa38e79f38e27ce7e 0xdd1c73cf9c713e73

def z848 : W := mkw 0x0c09144810012000 0x006048a240800900 0x5c0f9e7cf001c00d 0xd2e07cf3e7800e00

def z849 : W := mkw 0x0c39b6cd30db35b2 0x8061cdb66986d9ad 0xdc7fffff71fe3fff 0xfee3fffffb8ff1ff

def z850 : W := mkw 0x5b6de000699a0000 0x0adb6f00034cd000 0x7fffe000ffd80017 0xebffff0007fec000

def z851 : W := mkw 0xa4901f901241fe5d 0x052480fc80920ff2 0x80001f800001fe68 0x040000fc00000ff3

def z852 : W := mkw 0x008209108624ca45 0x0004104884312652 0xa38019808e01cc1a 0xcd1c00cc04700e60

def z853 : W := mkw 0x0c29b44d00000000 0x00614da268000000 0x5c0ffe7f0000000d 0xd2e07ff3f8000000

def z854 : W := mkw 0x0c09144800000000 0x006048a240000000 0xdc0f9e7c0000301d 0xf6e07cf3e0000180

def z855 : W := mkw 0x0c1916c800401410 0x0060c8b6400200a0 0xdc7f9ffc01c03c1f 0xfee3fcffe00e01e0

def z856 : W := mkw 0x00020010f9bb6306 0x0800100087cddb18 0x80000000f1f9f390 0x24000000078fcf9c

def z857 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e79f38e07cc6e 0xd91c73cf9c703e63

def z858 : W := mkw 0x0c09144810012000 0x006048a240800900 0xdc0f9e7cf039f39d 0xf6e07cf3e781cf9c

def z859 : W := mkw 0xfffdffc85b41bc18 0x07ffeffe42da0de0 0xfffffffcffc1fc1f 0xffffffffe7fe0fe0

def z860 : W := mkw 0x7fedfd6f00000000 0x13ff6feb78000000 0x7f8e787300000000 0x83fc73c398000000

def z861 : W := mkw 0xfffdffea5b41bc18 0x17ffefff52da0de0 0xfffffff0ffc1fc1f 0xefffffff87fe0fe0

def z862 : W := mkw 0xb6d01f855b41bcb8 0x85b680fc2ada0de5 0xfff07f8fffe7ffff 0xffff83fc7fff3fff

def z863 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff00060c6f 0xdbfffffff8003063

def z864 : W := mkw 0x13464000edbe0000 0x089a3200076df000 0x7ffe6000fffe0017 0xebfff30007fff000

def z865 : W := mkw 0xb6d21f90df65fe5d 0x05b690fc86fb2ff2 0xfff01f80ffc1fc1b 0xefff80fc07fe0fe0

def z866 : W := mkw 0xfffdffef59cb34b8 0x97ffefff7ace59a5 0xffffffff71fe3fff 0xfffffffffb8ff1ff

def z867 : W := mkw 0x0184492206048841 0x000c224910302442 0x238e79f30e060c62 0x891c73cf98703063

def z868 : W := mkw 0x5f6df4484d8e0000 0x0afb6fa2426c7000 0x7ffffe7c0fc6000f 0xdbfffff3e07e3000

def z869 : W := mkw 0x000200108220ca45 0x0000100084110652 0x800000008021ce70 0x0400000004010e73

def z870 : W := mkw 0x13c4492200000000 0x009e224910000000 0x7ffe79f30000000f 0xd3fff3cf98000000

def z871 : W := mkw 0x00020010b231eb06 0x0000100085918f58 0x80000000fe39ff90 0x2c00000007f1cffc

def z872 : W := mkw 0x492de06f008a00a0 0x92496f0378045005 0x000fe07f00060064 0x10007f03f8003003

def z873 : W := mkw 0x0c891d6a00000000 0x006448eb50000000 0x5c0f9fff0000000d 0xd2e07cfff8000000

def z874 : W := mkw 0x7bfdebef00000000 0x13dfef5f78000000 0x23fe61f300000002 0x011ff30f98000000

def z875 : W := mkw 0x2d9d5fef00000000 0x116ceaff78000000 0x7f8fffff0000000f 0xd3fc7ffff8000000

def z876 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0ffe7cf03ff39f 0xfee07ff3e781ff9c

def z877 : W := mkw 0x1240000049000000 0x0092000002480000 0x7ff00000ffc00001 0xa3ff800007fe0000

def z878 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9e7cf039f391 0xa6e07cf3e781cf9c

def z879 : W := mkw 0x7e49144800000000 0x13f248a240000000 0x5c0e187000000000 0x82e070c380000000

def z880 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff0018318f 0xf3fffffff800c18c

def z881 : W := mkw 0xffcd5d6a5b01a808 0x17fe6aeb52d80d40 0xff8f9e7cfe01f01d 0xf7fc7cf3e7f00f80

def z882 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0xffffffff01c63fef 0xdffffffff80e31ff

def z883 : W := mkw 0x4d3df6ef00ca14b0 0x9269efb7780650a5 0xdc7fffff01fe3fff 0xfee3fffff80ff1ff

def z884 : W := mkw 0x493de2ef00000000 0x1249ef1778000000 0x000fe7ff0000000c 0x10007f3ff8000000

def z885 : W := mkw 0x0032a295a0fa57b6 0x80019514ad07d2bd 0x8071e78f01fe3fff 0x7c038f3c780ff1ff

def z886 : W := mkw 0x4d0d546a00000000 0x12686aa350000000 0x5c0f9e7c0000000d 0xd2e07cf3e0000000

def z887 : W := mkw 0x0c891d4800000000 0x006448ea40000000 0x7f8f9ffc0000000f 0xd3fc7cffe0000000

def z888 : W := mkw 0x493de2ef00000000 0x1249ef1778000000 0x007fe1ff00000006 0x1003ff0ff8000000

def z889 : W := mkw 0xb6d21f90ffffff1e 0x0db690fc87fffff8 0xfff01f80ffffff9b 0xefff80fc07fffffc

def z890 : W := mkw 0x0839a2cd00ca14b0 0x8041cd16680650a5 0x807fe7ff01fe3fff 0x7c03ff3ff80ff1ff

def z891 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc7f9e7cf1f9f39f 0xfee3fcf3e78fcf9c

def z892 : W := mkw 0x00020010fdbf6306 0x0800100087edfb18 0x00000000ffffc010 0x2800000007fffe00

def z893 : W := mkw 0x6d9d5fef00000000 0x136ceaff78000000 0x000e1fff00000008 0x100070fff8000000

def z894 : W := mkw 0x5260a000498a0000 0x0a930500024c5000 0x7ff00000ffc00013 0xebff800007fe0000

def z895 : W := mkw 0x7ffdffef008a00a0 0x93ffefff78045005 0xffffffff003e0fff 0xdffffffff801f07f

def z896 : W := mkw 0xffedfd6a5b01a808 0x17ff6feb52d80d40 0x7ffff870ffc1c017 0xebffffc387fe0e00

def z897 : W := mkw 0x0c09144830112102 0x006048a241808908 0x5c0f9e7c7000000d 0xd2e07cf3e3800000

def z898 : W := mkw 0x0002001084244204 0x0000100084212210 0x800000008e27c210 0x0c00000004713e10

def z899 : W := mkw 0x0c09144810012000 0x006048a240800900 0xdc0f9e7c0001f00d 0xd6e07cf3e0000f80

def z900 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0xffff9ffcffc1fc1b 0xeffffcffe7fe0fe0

def z901 : W := mkw 0xfffdffef59413418 0x17ffefff7aca09a0 0xffffffff71c03c1f 0xfffffffffb8e01e0

def z902 : W := mkw 0x0809004800000000 0x0040480240000000 0x000f867c0000000d 0x50007c33e0000000

def z903 : W := mkw 0xbec91d485b01a808 0x05f648ea42d80d40 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z904 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80007f830027fe7e 0x5c0003fc18013ff3

def z905 : W := mkw 0x0d8d5d6a3615a943 0x006c6aeb51b0ad4a 0x7f81e78f7e1e3de3 0x2bfc0f3c7bf0f1ef

def z906 : W := mkw 0x7ffdffef699a0000 0x1bffefff7b4cd000 0x7fffffffffd8001f 0xfbfffffffffec000

def z907 : W := mkw 0x13464000cd240000 0x009a320006692000 0x7ffe0000ffc00013 0xebfff00007fe0000

def z908 : W := mkw 0x12420010f9316306 0x0092100087c98b18 0xfff00000fff9f393 0xefff800007ffcf9c

def z909 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80001f8c0001ff88 0x140000fc60000ffc

def z910 : W := mkw 0x7ffdffef00ca1410 0x13ffefff780650a0 0xffffffff01fe3c1f 0xfffffffff80ff1e0

def z911 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe183fffe0c77 0xebffff0c1ffff063

def z912 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80000000f03ffff0 0x2c0000000781ffff

def z913 : W := mkw 0x0809004800000000 0x0040480240000000 0x5c0f807c00000005 0xd2e07c03e0000000

def z914 : W := mkw 0x12420000e9300000 0x0092100007498000 0x7ff00000fff80013 0xebff800007ffc000

def z915 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x000fe1ff0000000e 0x50007f0ff8000000

def z916 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x807fffff01fe3fff 0xfc03fffff80ff1ff

def z917 : W := mkw 0xbe5916c859413418 0x05f2c8b642ca09a0 0x5c7f9e7c71c0300d 0xf2e3fcf3e38e0180

def z918 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe000ffd80007 0xe3ffff0007fec000

def z919 : W := mkw 0x008209328624ca45 0x0004104994312652 0x800001838e27ce70 0x0c00000c1c713e73

def z920 : W := mkw 0xffdd5fea1241bc18 0x17feeaff50920de0 0xff8e1ff00001fc08 0x87fc70ff80000fe0

def z921 : W := mkw 0x000200109625eb47 0x0000100084b12f5a 0x800000008e27fff0 0x0c00000004713fff

def z922 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e19f300000008 0x93fc70cf98000000

def z923 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0xfffffffffff9ff9f 0xffffffffffffcffc

def z924 : W := mkw 0xb6d01f855b41bcb8 0x85b680fc2ada0de5 0xfff01f83ffc1fc7b 0xefff80fc1ffe0fe3

def z925 : W := mkw 0x0184492202008800 0x000c224910100440 0xa38e19f08e01cc1a 0xcd1c70cf84700e60

def z926 : W := mkw 0x80020010cf64de5d 0x04001000867b26f2 0x800000008fe7ce70 0x0c000000047f3e73

def z927 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e18700000000c 0xd3fc70c380000000

def z928 : W := mkw 0x5a69a000699a0000 0x0ad34d00034cd000 0x7ff180007fd80003 0x2bff8c0003fec000

def z929 : W := mkw 0x5364e00049000000 0x029b270002480000 0x7ff06000ffc00013 0xebff830007fe0000

def z930 : W := mkw 0x8032a295fbfbffbe 0x84019514afdfdffd 0x8071e78fffffffff 0x7c038f3c7fffffff

def z931 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7ff1e000fffe0013 0x2bff8f0007fff000

def z932 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0xa3f1e78f8ffe3fff 0xfd1f8f3c7c7ff1ff

def z933 : W := mkw 0x7fcd5d6a49000000 0x13fe6aeb52480000 0x7ffe1870ffc00013 0xebfff0c387fe0000

def z934 : W := mkw 0x3e5916c800000000 0x01f2c8b640000000 0x5c7f9e7c0000000d 0xd2e3fcf3e0000000

def z935 : W := mkw 0x80020010b271ff1e 0x0400100085938ff8 0x80000000f039ff90 0x240000000781cffc

def z936 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff19f8cffc1fc1f 0xffff8cfc67fe0fe0

def z937 : W := mkw 0x7f7df6ef00000000 0x13fbefb778000000 0x5c7fe7ff0000000f 0x52e3ff3ff8000000

def z938 : W := mkw 0x5f4d544800000000 0x02fa6aa240000000 0x7f8e187000000000 0x83fc70c380000000

def z939 : W := mkw 0x49ade96f00000000 0x124d6f4b78000000 0x000ff9ff0000000c 0x10007fcff8000000

def z940 : W := mkw 0x0829a04d00000000 0x00414d0268000000 0x000fe07f00000004 0x10007f03f8000000

def z941 : W := mkw 0x0dbdffef00ca14b0 0x806defff780650a5 0xffffffff01fe3fff 0xfffffffff80ff1ff

def z942 : W := mkw 0x5b6fe04dedbe0000 0x1adb7f026f6df000 0x7fffe00cfffe0017 0xebffff0067fff000

def z943 : W := mkw 0x134440004d040000 0x009a220002682000 0x7ff06000ffc60013 0xebff830007fe3000

def z944 : W := mkw 0x6dbdffef00000000 0x136defff78000000 0x5c0fffff0000000d 0xd2e07ffff8000000

def z945 : W := mkw 0x0d8d5d6a00000000 0x006c6aeb50000000 0x7f8f9e7c0000000d 0xd3fc7cf3e0000000

def z946 : W := mkw 0x4d2df46f10012000 0x12696fa378800900 0xdc0ffe7ff001f01d 0xf6e07ff3ff800f80

def z947 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0xffffffff01c63c7f 0xfffffffff80e31e3

def z948 : W := mkw 0x00020010fd356306 0x0800100087e9ab18 0x80000000fe39f390 0x2400000007f1cf9c

def z949 : W := mkw 0xff7df6ef59413418 0x17fbefb77aca09a0 0x5c7fe67f71c03005 0x32e3ff33fb8e0180

def z950 : W := mkw 0x5b6fe06fedbe00a0 0x9adb7f037f6df005 0x7fffe07ffffe03f7 0xfbffff03fffff01f

def z951 : W := mkw 0x7fcd5d6a30112102 0x13fe6aeb51808908 0x7f8f9e7c70183181 0xa3fc7cf3e380c18c

def z952 : W := mkw 0xa4b0bf8512cbbcb8 0x852585fc28965de5 0x8001ff8f003fffec 0x14000ffc7801ffff

def z953 : W := mkw 0xffcd5d6a1201a808 0x17fe6aeb50900d40 0x7f8e18700001c000 0x83fc70c380000e00

def z954 : W := mkw 0x2c991fef00000000 0x1164c8ff78000000 0x000f9fff0000000c 0x10007cfff8000000

def z955 : W := mkw 0x05845d6a00000000 0x002c22eb50000000 0x238e7fff0000000e 0xd11c73fff8000000

def z956 : W := mkw 0x5a6ba000edbe0000 0x0ad35d00076df000 0x7ff18000fffe0013 0xebff8c0007fff000

def z957 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xffffe000fffe0e77 0xefffff0007fff073

def z958 : W := mkw 0x5bfdeba700000000 0x02dfef5d38000000 0x7fffffff0000000f 0xd3fffffff8000000

def z959 : W := mkw 0x7fcd5d6a4d040000 0x1bfe6aeb52682000 0x7f8e18700e000000 0x83fc70c380700000

def z960 : W := mkw 0x6dbdffef00ca14b0 0x936defff780650a5 0x800fffff003e3fec 0x14007ffff801f1ff

def z961 : W := mkw 0x7ffdffef498a0000 0x13ffefff7a4c5000 0x7ffffffffffe001f 0xfbfffffffffff000

def z962 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e79f38e3ffffe 0xfd1c73cf9c71ffff

def z963 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fffffff01c0000f 0xd3fffffff80e0000

def z964 : W := mkw 0x0c09144830112102 0x006048a241808908 0x5c0f9e7c70183181 0xa2e07cf3e380c18c

def z965 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9e7c7039f38d 0x36e07cf3e381cf9c

def z966 : W := mkw 0x00020010a0304306 0x0000100085018218 0x800000008039c390 0x040000000401ce1c

def z967 : W := mkw 0x00020010b635eb47 0x0000100085b1af5a 0x80000000fe27ce70 0x0c00000007f13e73

def z968 : W := mkw 0xbed91fc87b51bd1a 0x05f6c8fe43da8de8 0xffff9ffcffd9fd9f 0xfffffcffe7fecfec

def z969 : W := mkw 0x1240000049000000 0x0092000002480000 0xfff00180ffc00c1b 0xefff800c07fe0060

def z970 : W := mkw 0x5b6de02200000000 0x02db6f0110000000 0x7fffe07300000007 0xd3ffff0398000000

def z971 : W := mkw 0x5bede96f00000000 0x12df6f4b78000000 0x7ffff9ff0000000f 0xd3ffffcff8000000

def z972 : W := mkw 0x7fdd5fef00000000 0x13feeaff78000000 0x7f8e7fff0000000e 0xd3fc73fff8000000

def z973 : W := mkw 0x7e79b6cd00ca14b0 0x93f3cdb6680650a5 0xdc7f9e7c01f8339d 0xf6e3fcf3e00fc19c

def z974 : W := mkw 0x36d01f8000000000 0x01b680fc00000000 0x7ffe1ff00000000f 0xd3fff0ff80000000

def z975 : W := mkw 0x492de06f20100102 0x12496f0379008008 0x000fe07f00180184 0x10007f03f800c00c

def z976 : W := mkw 0x5366e000edbe0000 0x0a9b3700076df000 0x7ff06000fffe0013 0xebff830007fff000

def z977 : W := mkw 0x80020010df65fe5d 0x0400100086fb2ff2 0x80000000ffc1fc10 0x2c00000007fe0fe0

def z978 : W := mkw 0x00020010a0304306 0x0000100085018218 0x8000000000383390 0x240000000001c19c

def z979 : W := mkw 0x5bede9224b008800 0x02df6f4912580440 0xfffff9f3ffc1cc1f 0xffffffcf9ffe0e60

def z980 : W := mkw 0x7ffdffef02008841 0x13ffefff78100442 0x7fffffff00000c6f 0xd3fffffff8000063

def z981 : W := mkw 0x00020010b635eb47 0x0000100085b1af5a 0x80000000fe39f390 0x2400000007f1cf9c

def z982 : W := mkw 0xfffdffef4f449c59 0x17ffefff7a7a24e2 0x7fffffff0fc60c6f 0xdbfffffff87e3063

def z983 : W := mkw 0x0002001084ee56f5 0x80001000842772b7 0x8000000001fe3ff0 0x2c000000000ff1ff

def z984 : W := mkw 0x0022a01584ae42e5 0x80011500ac257217 0x0001e00f003e03e4 0x10000f007801f01f

def z985 : W := mkw 0x0184496f00000000 0x100c224b78000000 0x238e79ff0000000e 0xd11c73cff8000000

def z986 : W := mkw 0x5bede922008a0000 0x02df6f4910045000 0xfffff9f301fe0e7f 0xffffffcf980ff073

def z987 : W := mkw 0xfffdffef1201a808 0x17ffefff78900d40 0x7fffffff0001c00f 0xd3fffffff8000e00

def z988 : W := mkw 0x1a4b0000e9300000 0x00d2580007498000 0x7ffe0000ffc00013 0xebfff00007fe0000

def z989 : W := mkw 0x0002001084244245 0x0000100084212212 0x0000600300260264 0x1000030018013013

def z990 : W := mkw 0xb6d01fea5b41bc18 0x15b680ff52da0de0 0xfff01ff0ffc1fc1b 0xefff80ff87fe0fe0

def z991 : W := mkw 0x008209108220ca04 0x0004104884110650 0xa38e79f38e27ce7e 0xdd1c73cf9c713e73

def z992 : W := mkw 0x492fe07aa4be4347 0x0a497f03d525f21a 0x000fe07f003e03e4 0x10007f03f801f01f

def z993 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f9e7c00000001 0x82e07cf3e0000000

def z994 : W := mkw 0x493de2ef00000000 0x1249ef1778000000 0x007fe67f00000005 0x1003ff33f8000000

def z995 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800000008e01cc10 0x0c00000004700e60

def z996 : W := mkw 0x080b0058a0304306 0x00405802c5018218 0x0001800c00380380 0x00000c006001c01c

def z997 : W := mkw 0x1a4b0058e9304306 0x00d25802c7498218 0x7fff807cfff80397 0xfbfffc03e7ffc01c

def z998 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8fffff0000000f 0xd3fc7ffff8000000

def z999 : W := mkw 0x5b6fe032edbe4245 0x0adb7f01976df212 0x7fffe070fffe0017 0xebffff0387fff000

def z1000 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01980ffc1fc12 0xafff80cc07fe0fe0

def z1001 : W := mkw 0x5bede922699a0000 0x0adf6f49134cd000 0x7ffff9f371d8000f 0xf3ffffcf9b8ec000

def z1002 : W := mkw 0xb6c21d10df25ea4d 0x05b610e886f92f52 0x7f801800fe01c000 0x83fc00c007f00e00

def z1003 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c01860c70383381 0x22e00c306381c19c

def z1004 : W := mkw 0x00020010ef34ca45 0x080010008779a652 0x00000000fe01c000 0x0000000007f00e00

def z1005 : W := mkw 0x0c09144830112102 0x006048a241808908 0xdc0f9e7c7038339d 0xf6e07cf3e381c19c

def z1006 : W := mkw 0x7f7df6ef00000000 0x13fbefb778000000 0x5c7ffe7f0000000d 0xd2e3fff3f8000000

def z1007 : W := mkw 0xb6c01d005b01a808 0x05b600e802d80d40 0xfff01980ffc1cc1b 0xefff80cc07fe0e60

def z1008 : W := mkw 0x12420000cd240000 0x0092100006692000 0x7ff00000ffe60013 0xebff800007ff3000

def z1009 : W := mkw 0x25945fef00000000 0x112ca2ff78000000 0x238e1fff00000008 0x911c70fff8000000

def z1010 : W := mkw 0x7ffdffef69da14b0 0x9bffefff7b4ed0a5 0xffffffff71fe3fff 0xfffffffffb8ff1ff

def z1011 : W := mkw 0xac991fc81241bc18 0x0564c8fe40920de0 0xdc0f9ffc0001fc0d 0xd6e07cffe0000fe0

def z1012 : W := mkw 0x6dbdffef00000000 0x136defff78000000 0x238fffff0000000e 0xd11c7ffff8000000

def z1013 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fffffff01fe0fef 0xdbfffffff80ff07f

def z1014 : W := mkw 0x0104402200000000 0x0008220110000000 0x000e007000000000 0x0000700380000000

def z1015 : W := mkw 0x1240000049000000 0x0092000002480000 0x7ff00000ffc00002 0x8bff800007fe0000

def z1016 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e7ff38e27fe7f 0xfd1c73ff9c713ff3

def z1017 : W := mkw 0x7ffdffef4b008800 0x13ffefff7a580440 0xffffffffffc1cc1f 0xfffffffffffe0e60

def z1018 : W := mkw 0x0c0b1458b635eb47 0x006058a2c5b1af5a 0xdc01860cfe3ffff1 0x2ee00c3067f1ffff

def z1019 : W := mkw 0x7fedfd6a00000000 0x13ff6feb50000000 0x7ffe787000000002 0x83fff3c380000000

def z1020 : W := mkw 0x3ed91fef00000000 0x11f6c8ff78000000 0x7fff9fff0000000f 0xd3fffcfff8000000

def z1021 : W := mkw 0x00020010b4356347 0x0000100085a1ab1a 0x80000000f03ff3f0 0x240000000781ff9f

def z1022 : W := mkw 0x4d2df46f00000000 0x12696fa378000000 0x000ffe7f0000000c 0x10007ff3f8000000

def z1023 : W := mkw 0xedbfff80b6ffbc18 0x0f6dfffc05b7fde0 0x800fff80003ffc0c 0x04007ffc0001ffe0

def z1024 : W := mkw 0x7ffdffef008a0000 0x13ffefff78045000 0xffffffff01fe0e7f 0xfffffffff80ff073

def z1025 : W := mkw 0x0c1916cd00000000 0x0060c8b668000000 0x5c0f9fff0000000d 0xd2e07cfff8000000

def z1026 : W := mkw 0x5b6fe048edbe0000 0x0adb7f02476df000 0x7fffe07cfffe0017 0xfbffff03e7fff000

def z1027 : W := mkw 0x0002001080204204 0x0000100084010210 0x0000000000200200 0x0000000000010010

def z1028 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x007fe07f00000007 0x5003ff03f8000000

def z1029 : W := mkw 0x0809004800000000 0x0040480240000000 0x000e007000000000 0x0000700380000000

def z1030 : W := mkw 0x040214109625ea45 0x002010a084b12f52 0xdc001e00fe27fe79 0xeee000f007f13ff3

def z1031 : W := mkw 0x5a69a000699a0000 0x0ad34d00034cd000 0x7ff18000ffd80001 0xa3ff8c0007fec000

def z1032 : W := mkw 0xa4901fcd1241bc18 0x152480fe68920de0 0x80001f8c0001fc08 0x040000fc60000fe0

def z1033 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x000fe07f00260264 0x10007f03f8013013

def z1034 : W := mkw 0xb6d01fef5b41bcb8 0x95b680ff7ada0de5 0xfff01fffffc1fffb 0xffff80fffffe0fff

def z1035 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9e7cf019f389 0xb6e07cf3e780cf9c

def z1036 : W := mkw 0x7ffdffef4dce14b0 0x9bffefff7a6e70a5 0x7fffffff0fc60c6f 0xdbfffffff87e3063

def z1037 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe60cfffe001f 0xfbffff3067fff000

def z1038 : W := mkw 0x7ffdffef49000000 0x13ffefff7a480000 0x7ffffffffe00000f 0xd3fffffffff00000

def z1039 : W := mkw 0x80120290df65fe5d 0x0400901486fb2ff2 0x80706783ffe7fe7f 0x7c03833c1fff3ff3

def z1040 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80001f808001fc18 0xc40000fc04000fe0

def z1041 : W := mkw 0x12420010cf24ca45 0x0092100086792652 0xfff00000ffe7ce73 0xefff800007ff3e73

def z1042 : W := mkw 0x1a4b0000edbe0000 0x08d25800076df000 0x7fff8000fffe0017 0xebfffc0007fff000

def z1043 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01e00ffc1f019 0xe7ff80f007fe0f80

def z1044 : W := mkw 0x492de06f00ca14b0 0x92496f03780650a5 0x800fe07f01fe3ff4 0x3c007f03f80ff1ff

def z1045 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80000000f001f010 0x2400000007800f80

def z1046 : W := mkw 0x5b6fe005edbe0000 0x0adb7f002f6df000 0x7fffe00ffffe0017 0xfbffff007ffff000

def z1047 : W := mkw 0x7ffdffef02008800 0x13ffefff78100440 0xffffffff0001cc0f 0xd7fffffff8000e60

def z1048 : W := mkw 0x5f6df46f00000000 0x12fb6fa378000000 0x7ffffe7f0000000f 0xd3fffff3f8000000

def z1049 : W := mkw 0xffcd5d6a4b008808 0x17fe6aeb52580440 0x7f8e18700e000000 0x83fc70c380700000

def z1050 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fff8000ffd80013 0xebfffc0007fec000

def z1051 : W := mkw 0x7fdd5fea00000000 0x13feeaff50000000 0x7ffe7ff30000000f 0xd3fff3ff98000000

def z1052 : W := mkw 0x00020010a0ba43a6 0x800010008505d21d 0x00000000003e03e0 0x000000000001f01f

def z1053 : W := mkw 0x0d8d5d6a30112102 0x006c6aeb51808908 0x7f8fffff7018318f 0xf3fc7ffffb80c18c

def z1054 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80001f800001fc19 0x640000fc00000fe0

def z1055 : W := mkw 0x493de2ef00401410 0x1249ef17780200a0 0x807fe7ff01c03c1f 0x7c03ff3ff80e01e0

def z1056 : W := mkw 0x5b6de06f699a0000 0x1adb6f037b4cd000 0x5c7fe07f71d80005 0x32e3ff03fb8ec000

def z1057 : W := mkw 0x7f7df6ef00ca14b0 0x93fbefb7780650a5 0xdc7fe7ff01fe3fff 0x7ee3ff3ff80ff1ff

def z1058 : W := mkw 0x5f6df44859012000 0x02fb6fa242c80900 0xfffffe7cffc1f01f 0xfffffff3e7fe0f80

def z1059 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa3fe79f38fe7ce7f 0xfd1ff3cf9c7f3e73

def z1060 : W := mkw 0x7fcd5d6a10012000 0x13fe6aeb50800900 0xff8e1e70f001f019 0xe7fc70f387800f80

def z1061 : W := mkw 0x6dbdffef00000000 0x136defff78000000 0x007fffff0000000f 0x5003fffff8000000

def z1062 : W := mkw 0x0104402200000000 0x0008220110000000 0x000e78730000000c 0xd00073c398000000

def z1063 : W := mkw 0xb65016805b41bc18 0x05b280b402da0de0 0xfff00600ffc1fc13 0xefff803007fe0fe0

def z1064 : W := mkw 0x5b4d406a00000000 0x12da6a0350000000 0x7f8e007000000000 0x83fc700380000000

def z1065 : W := mkw 0x12420000c9200000 0x0092100006490000 0x7ffe0000ffe00017 0xebfff00007ff0000

def z1066 : W := mkw 0x492de02200000000 0x02496f0110000000 0x000fe07300000004 0x10007f0398000000

def z1067 : W := mkw 0x0010028000401410 0x00008014000200a0 0x8071e78f01fe3fff 0x7c038f3c780ff1ff

def z1068 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fffffff01fe0c7f 0xfbfffffff80ff063

def z1069 : W := mkw 0x490d406f00000000 0x12486a0378000000 0x000e007f00000000 0x10007003f8000000

def z1070 : W := mkw 0x36d21f90b0316306 0x01b690fc85818b18 0xfff01f80f039f39b 0xe7ff80fc0781cf9c

def z1071 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e18700000000c 0xd11c70c380000000

def z1072 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071e78f01fe3ff3 0x2c038f3c780ff1ff

def z1073 : W := mkw 0xbedb1fd8fb71ff1e 0x05f6d8fec7db8ff8 0xfff19f8cfff9ff9b 0xefff8cfc67ffcffc

def z1074 : W := mkw 0x7fedfd6f008a00a0 0x93ff6feb78045005 0x7f8ff87f003e03e4 0x93fc7fc3f801f01f

def z1075 : W := mkw 0x7ef9bfef00000000 0x13f7cdff78000000 0x5c7f9fff0000000d 0xd2e3fcfff8000000

def z1076 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0xdc71e78ff1fe3fff 0xfee38f3c7f8ff1ff

def z1077 : W := mkw 0xfffdffef4b008808 0x17ffefff7a580440 0x7fffffff0e00000f 0xd3fffffff8700000

def z1078 : W := mkw 0xfffdffef4bca9cb8 0x97ffefff7a5e54e5 0xffffffff0ffe3fff 0xfffffffff87ff1ff

def z1079 : W := mkw 0x492de06f000000a0 0x92496f0378000005 0x000fe07f000003e4 0x10007f03f800001f

def z1080 : W := mkw 0x7fedfd6a00000000 0x13ff6feb50000000 0x7ffff9f30000000f 0xd3ffffcf98000000

def z1081 : W := mkw 0x04901fff1241fff7 0x802480fff8920fff 0x80001fff0001ffe8 0x140000fff8000fff

def z1082 : W := mkw 0x0184492202008841 0x000c224910100442 0x238e79f300000c6e 0xd11c73cf98000063

def z1083 : W := mkw 0x5b6de0006d9e0000 0x0adb6f00036cf000 0x7ff1e000ffde0013 0xebff8f0007fef000

def z1084 : W := mkw 0x5b6fe037edbe42e5 0x8adb7f01bf6df217 0x7fffe07ffffe03f7 0xfbffff03fffff01f

def z1085 : W := mkw 0xb7c45d225b01a808 0x05be22e912d80d40 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z1086 : W := mkw 0x092fe000a4be0000 0x00497f000525f000 0x7fffe000fffe0017 0xebffff0007fff000

def z1087 : W := mkw 0x0c09145830116306 0x006048a2c1808b18 0xdc0f9e7c7019f38d 0xf6e07cf3e380cf9c

def z1088 : W := mkw 0x5b6fe058edbe4306 0x0adb7f02c76df218 0xfffff87cffffc39f 0xffffffc3e7fffe1c

def z1089 : W := mkw 0x1262a000edbe0000 0x08931500076df000 0x7ff1e000fffe0017 0xebff8f0007fff000

def z1090 : W := mkw 0x7ffdffef59012000 0x13ffefff7ac80900 0xffffffffffc1f01f 0xfffffffffffe0f80

def z1091 : W := mkw 0xfffdffef5fcfbc18 0x1fffefff7afe7de0 0xffffffffffc7fc1f 0xfffffffffffe3fe0

def z1092 : W := mkw 0x090d406a00000000 0x00486a0350000000 0x000fe07f00000004 0x10007f03f8000000

def z1093 : W := mkw 0x12400000699a0000 0x08920000034cd000 0x7ff00000ffd80013 0xebff800007fec000

def z1094 : W := mkw 0x0432b695b0fb77b6 0x802195b4ad87dbbd 0xdc71ff8ff1ffffff 0xfee38ffc7f8fffff

def z1095 : W := mkw 0x7ffdffef00401410 0x13ffefff780200a0 0xffffffff01f83f9f 0xfffffffff80fc1fc

def z1096 : W := mkw 0x5a69a00049000000 0x02d34d0002480000 0x7ff18000ffc00013 0xebff8c0007fe0000

def z1097 : W := mkw 0x5f6df44800000000 0x02fb6fa240000000 0x7ffff87000000007 0xc3ffffc380000000

def z1098 : W := mkw 0x04021410b0316306 0x002010a085818b18 0xdc001e00f001f019 0xe6e000f007800f80

def z1099 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0xfffffffffe01fc0f 0xd7fffffffff00fe0

def z1100 : W := mkw 0x0032a295b0fb77b6 0x80019514ad87dbbd 0x80706183f1fffff2 0x2c03830c1f8fffff

def z1101 : W := mkw 0x0809004800000000 0x0040480240000000 0x000f987c0000000c 0xd0007cc3e0000000

def z1102 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff01e00ffc1f013 0xebff80f007fe0f80

def z1103 : W := mkw 0x492de06f008a0000 0x12496f0378045000 0x007fe07f01fe0017 0x7803ff03f80ff000

def z1104 : W := mkw 0x5b6fe027edbe0000 0x1adb7f013f6df000 0x7fffe003fffe0017 0xebffff001ffff000

def z1105 : W := mkw 0x0c09144810012000 0x006048a240800900 0x5c0f9e7c7000300d 0xf2e07cf3e3800180

def z1106 : W := mkw 0x098d492200000000 0x004c6a4910000000 0x7f8ff9f30000000f 0xd3fc7fcf98000000

def z1107 : W := mkw 0xfffdffef4b409c18 0x17ffefff7a5a04e0 0xffffffff0fc03c1f 0xfffffffff87e01e0

def z1108 : W := mkw 0x0002001090216306 0x0000100084810b18 0x800000008021f390 0x0400000004010f9c

def z1109 : W := mkw 0x7ffdffef06048841 0x13ffefff78302442 0xffffffff8e07cc7f 0xdffffffffc703e63

def z1110 : W := mkw 0x73f4eba700ca14b0 0x939fa75d380650a5 0xa3ffffff01fe3fff 0xfd1ffffff80ff1ff

def z1111 : W := mkw 0xa4901fb71241fefd 0x852480fdb8920ff7 0x80001fff0001ffe8 0x140000fff8000fff

def z1112 : W := mkw 0x5b6de000498a0000 0x02db6f00024c5000 0x7fffe000fffe0017 0xebffff0007fff000

def z1113 : W := mkw 0xfffdffef7b51bd1a 0x17ffefff7bda8de8 0xffffffffffd9fd9f 0xfffffffffffecfec

def z1114 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e7fff8e27fffe 0xdd1c73fffc713fff

def z1115 : W := mkw 0x000200108624ca45 0x0000100084312652 0x000000008e27c260 0x0000000004713e13

def z1116 : W := mkw 0x49ade92200000000 0x024d6f4910000000 0x238ff9f30000000e 0xd11c7fcf98000000

def z1117 : W := mkw 0x5b6fe010edbe4204 0x0adb7f00876df210 0xffffe000ffffc217 0xefffff0007fffe10

def z1118 : W := mkw 0x04021410b0316306 0x002010a085818b18 0xdc000600f039f391 0x26e000300781cf9c

def z1119 : W := mkw 0x1e49144849000000 0x00f248a242480000 0x7fff9e7cffc0001f 0xfbfffcf3e7fe0000

def z1120 : W := mkw 0x1240000049000000 0x0092000002480000 0x7ff18000fff80017 0xebff8c0007ffc000

def z1121 : W := mkw 0x0809004800000000 0x0040480240000000 0x000f807c00380384 0x10007c03e001c01c

def z1122 : W := mkw 0xb7f4ffa75bcbbcb8 0x85bfa7fd3ade5de5 0xffffffffffffffff 0xffffffffffffffff

def z1123 : W := mkw 0x7f7df6ef00000000 0x13fbefb778000000 0x7fffe67f00000007 0xd3ffff33f8000000

def z1124 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7ffe79f301c60c62 0x8bfff3cf980e3063

def z1125 : W := mkw 0x37f4ffa700ca14b0 0x81bfa7fd380650a5 0xffffffff01fe3fff 0xfffffffff80ff1ff

def z1126 : W := mkw 0x25945fa200000000 0x012ca2fd10000000 0x238e7ff30000000e 0xd11c73ff98000000

def z1127 : W := mkw 0x4d3df6ef00000000 0x1269efb778000000 0x5c7fffff0000000f 0xd2e3fffff8000000

def z1128 : W := mkw 0x0d0d546a00000000 0x00686aa350000000 0x5c0ffe7f0000000d 0xd2e07ff3f8000000

def z1129 : W := mkw 0x924000005b01a808 0x0492000002d80d40 0x7ff00000ffc1c013 0xebff800007fe0e00

def z1130 : W := mkw 0x492fe010a4be4204 0x0a497f008525f210 0x000fe070003e0204 0x10007f038001f010

def z1131 : W := mkw 0x5b6de06f00000000 0x12db6f0378000000 0x23ffe07f00000006 0x111fff03f8000000

def z1132 : W := mkw 0x7ffdffef004014b0 0x93ffefff780200a5 0xffffffff01c03fff 0xfffffffff80e01ff

def z1133 : W := mkw 0xa4901f851241bc18 0x052480fc28920de0 0x80001f8f0001fc08 0x140000fc78000fe0

def z1134 : W := mkw 0x0c29b448008a0000 0x00614da240045000 0x5c7ffe7c01fe001f 0xfae3fff3e00ff000

def z1135 : W := mkw 0x12c009004b008800 0x0096004802580440 0x7ff01800ffc1c013 0xebff80c007fe0e00

def z1136 : W := mkw 0x73f6ebb78624ca45 0x139fb75dbc312652 0xa3f061838e27ce72 0x0d1f830c1c713e73

def z1137 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7ffe187000000003 0xc3fff0c380000000

def z1138 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7ffff870fffe001f 0xfbffffc387fff000

def z1139 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fffffff01fe33ef 0xf3fffffff80ff19f

def z1140 : W := mkw 0x8032a295dfeffefd 0x84019514aeff7ff7 0x8071e78fffffffff 0x7c038f3c7fffffff

def z1141 : W := mkw 0x5b6de06f4d8e0000 0x1adb6f037a6c7000 0x23ffe07f0fc60006 0x191fff03f87e3000

def z1142 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80001f800001fc1a 0x4c0000fc00000fe0

def z1143 : W := mkw 0xfffdffef59413418 0x17ffefff7aca09a0 0xfffffffff1c1f01f 0xf7ffffffff8e0f80

def z1144 : W := mkw 0x1240000049000000 0x0092000002480000 0xfff06183ffe60e7f 0xffff830c1fff3073

def z1145 : W := mkw 0x7bfdebef00000000 0x13dfef5f78000000 0x7fffe1ff00000007 0xd3ffff0ff8000000

def z1146 : W := mkw 0x0c39b6cd00ca14b0 0x8061cdb6680650a5 0x5c7f9e7c01d8318d 0xf2e3fcf3e00ec18c

def z1147 : W := mkw 0x5f6df448799b2102 0x0afb6fa243ccd908 0x7ffffe7c71d8318f 0xf3fffff3e38ec18c

def z1148 : W := mkw 0x7ffdffef008a00a0 0x93ffefff78045005 0x7fffffff0018018f 0xd3fffffff800c00c

def z1149 : W := mkw 0xfffdffef7bdbbc18 0x1fffefff7bdedde0 0xffffffffffd9fc1f 0xfffffffffffecfe0

def z1150 : W := mkw 0xfffdffef49401418 0x17ffefff7a4a00a0 0x7fffffff01c0000f 0xd3fffffff80e0000

def z1151 : W := mkw 0x2c891d6a00000000 0x116448eb50000000 0x5c0f9e7c0000000d 0xd2e07cf3e0000000

def z1152 : W := mkw 0x7ffdffef49ca14b0 0x93ffefff7a4e50a5 0xfffffffffffe3fff 0xfffffffffffff1ff

def z1153 : W := mkw 0x7ffdffef49000000 0x13ffefff7a480000 0x7fffffff0fc0000f 0xdbfffffff87e0000

def z1154 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800018008e27ce78 0xcc0000c004713e73

def z1155 : W := mkw 0xb7c45d225b01a808 0x05be22e912d80d40 0x7f8e79f3fe01c00e 0xd3fc73cf9ff00e00

def z1156 : W := mkw 0x5b6fe06aedbe0000 0x1adb7f03576df000 0x7fffe070fffe0017 0xebffff0387fff000

def z1157 : W := mkw 0x0032a29586eedef5 0x80019514ac3776f7 0x8071860c8ffffff1 0x2c038c30647fffff

def z1158 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80000000f021c210 0x0400000007810e10

def z1159 : W := mkw 0x25845d6a00000000 0x112c22eb50000000 0x238e79f30000000e 0xd11c73cf98000000

def z1160 : W := mkw 0x3ed91fc800401410 0x01f6c8fe400200a0 0xffff9ffc01f83f9f 0xfffffcffe00fc1fc

def z1161 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff1ff8fffffffff 0xffff8ffc7fffffff

def z1162 : W := mkw 0xb6d01fcd5b41bc18 0x15b680fe6ada0de0 0xfff01f8cffc1fc1b 0xefff80fc67fe0fe0

def z1163 : W := mkw 0x000200109625ea45 0x0000100084b12f52 0x80000000fe27fe70 0x2c00000007f13ff3

def z1164 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01980ffc1cc1a 0xcfff80cc07fe0e60

def z1165 : W := mkw 0x0002001080ea56b4 0x80001000840752b5 0x8000000081fffff0 0x2c000000040fffff

def z1166 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01f80fff9ff9b 0xefff80fc07ffcffc

def z1167 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe00cfffe0397 0xfbffff0067fff01c

def z1168 : W := mkw 0x0000000000000000 0x0000000000000000 0x000e187000000000 0x800070c380000000

def z1169 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800060008e27ce76 0x4c00030004713e73

def z1170 : W := mkw 0x0104402200000000 0x0008220110000000 0x000e61f30000000e 0x5000730f98000000

def z1171 : W := mkw 0x5364e0004d8e0000 0x0a9b2700026c7000 0x7ff060007fc60003 0x2bff830003fe3000

def z1172 : W := mkw 0x01b4eba700ca14b0 0x800da75d380650a5 0x23ffffff01d8318f 0xf11ffffff80ec18c

def z1173 : W := mkw 0x492de06f048e0000 0x1a496f0378247000 0x000fe07f00060004 0x10007f03f8003000

def z1174 : W := mkw 0xa4921f90b271ff1e 0x052490fc85938ff8 0x80001f80f039ff98 0x240000fc0781cffc

def z1175 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0fffff0000000f 0xd2e07ffff8000000

def z1176 : W := mkw 0xa4901f901241fe1c 0x052480fc80920ff0 0x80001ff00001fe08 0x140000ff80000ff0

def z1177 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38079838e27ce7a 0xcd1c03cc1c713e73

def z1178 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8f987c00000004 0x93fc7cc3e0000000

def z1179 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e79f38e07ce6a 0x9d1c73cf9c703e73

def z1180 : W := mkw 0x00020010b0bb6306 0x000010008585db18 0x80000000f1fff390 0x2c000000078fff9c

def z1181 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffe7ff30000000b 0xc3fff3ff98000000

def z1182 : W := mkw 0x000200108624ca45 0x0000100084312652 0x8001860c8e3ffffd 0x7c000c306471ffff

def z1183 : W := mkw 0x04121690b0fb77b6 0x802090b48587dbbd 0xdc701f80f1fffffb 0xeee380fc078fffff

def z1184 : W := mkw 0x5b6fe010edbe4245 0x0adb7f00876df212 0x7fffe000fffe0277 0xebffff0007fff013

def z1185 : W := mkw 0x0809006f00000000 0x1040480378000000 0x000f807f00000004 0x10007c03f8000000

def z1186 : W := mkw 0xa4901fc81241bc18 0x052480fe40920de0 0x80001ffc0001fc08 0x140000ffe0000fe0

def z1187 : W := mkw 0x0dbdffef00000000 0x006defff78000000 0x7fffffff0000000f 0xd3fffffff8000000

def z1188 : W := mkw 0xa4901fff1241ff1e 0x152480fff8920ff8 0x80001fff0001ff88 0x140000fff8000ffc

def z1189 : W := mkw 0x7ffdffef799b2102 0x1bffefff7bccd908 0x7fffffff71d8318f 0xf3fffffffb8ec18c

def z1190 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fff9e7c01d83181 0xa3fffcf3e00ec18c

def z1191 : W := mkw 0x1260a000498a0000 0x00930500024c5000 0x7ff06000ffc60013 0xebff830007fe3000

def z1192 : W := mkw 0x490d406a00000000 0x12486a0350000000 0x000e607300000004 0x1000730398000000

def z1193 : W := mkw 0x4d2df46f00000000 0x12696fa378000000 0x5c0ff87f00000004 0x92e07fc3f8000000

def z1194 : W := mkw 0xa4901fef1241bcb8 0x952480ff78920de5 0x80001fff0001ffe8 0x140000fff8000fff

def z1195 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e787300000004 0x911c73c398000000

def z1196 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x5c0fe07f00000005 0xd2e07f03f8000000

def z1197 : W := mkw 0x5b6de06f008a00a0 0x92db6f0378045005 0x7fffe07f01fe03f7 0xfbffff03f80ff01f

def z1198 : W := mkw 0x04021410b0316306 0x002010a085818b18 0xdc019e0cf039f39d 0xf6e00cf06781cf9c

def z1199 : W := mkw 0x80020010fbfbffbe 0x8400100087dfdffd 0x80000000fffffff0 0x2c00000007ffffff

def z1200 : W := mkw 0x5a6ba000e9ba0000 0x0ad35d00074dd000 0x7fff8000fff80017 0xebfffc0007ffc000

def z1201 : W := mkw 0x492fe010a4be4245 0x0a497f008525f212 0x000fe000003e0264 0x00007f000001f013

def z1202 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e1e7c00000008 0x93fc70f3e0000000

def z1203 : W := mkw 0x7ffdffef30112102 0x13ffefff79808908 0xffffffff7038339f 0xf7fffffffb81c19c

def z1204 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7f8fffff0000000c 0x93fc7ffff8000000

def z1205 : W := mkw 0x7f4d546a00000000 0x13fa6aa350000000 0x5c0e007000000000 0x02e0700380000000

def z1206 : W := mkw 0x01b6ebb786eedef5 0x800db75dbc3776f7 0xa3f061838ffffff2 0x2d1f830c1c7fffff

def z1207 : W := mkw 0x0032a295b0fb77b6 0x80019514ad87dbbd 0x8071860cf1f9f391 0x24038c30678fcf9c

def z1208 : W := mkw 0x5ae9a9326b9aca45 0x0ad74d49935cd652 0xdc7199f371d9ce69 0x36e38ccf9b8ece73

def z1209 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80001f830001fe68 0x140000fc18000ff3

def z1210 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7ffe6000fffe0012 0xabfff30007fff000

def z1211 : W := mkw 0xfe79b6cd59cb34b8 0x97f3cdb66ace59a5 0x5c71860c71d83181 0x22e38c30638ec18c

def z1212 : W := mkw 0x0002001086eedef5 0x80001000843776f7 0x800000008fe7ce70 0x0c000000047f3e73

def z1213 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe60cfffe3197 0xebffff3067fff18c

def z1214 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe003fffe0277 0xfbffff001ffff013

def z1215 : W := mkw 0x7fedfd6f00000000 0x13ff6feb78000000 0x7f8ffe7f0000000d 0xd3fc7ff3f8000000

def z1216 : W := mkw 0x7e7bb6ddb0316306 0x13f3ddb6ed818b18 0xdc71860cf039f391 0x26e38c306781cf9c

def z1217 : W := mkw 0xa4901fff1241fe5d 0x152480fff8920ff2 0x80001fff0001fe68 0x140000fff8000ff3

def z1218 : W := mkw 0x0002001084ae42e5 0x8000100084257217 0x00000000003e03e0 0x000000000001f01f

def z1219 : W := mkw 0x5bcd492200000000 0x02de6a4910000000 0x7f8e187000000000 0x83fc70c380000000

def z1220 : W := mkw 0x00020010b231eb47 0x0000100085918f5a 0x80000000f039fff0 0x240000000781cfff

def z1221 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe000ffde0003 0xabffff0007fef000

def z1222 : W := mkw 0x5a6ba010f9bb6306 0x0ad35d0087cddb18 0xdc718000f1f9f391 0x26e38c00078fcf9c

def z1223 : W := mkw 0x0400140010012000 0x002000a000800900 0xdc0e1e70f001f01d 0xf6e070f387800f80

def z1224 : W := mkw 0x01b4eba700000000 0x000da75d38000000 0x23fe79f30000000e 0xd11ff3cf98000000

def z1225 : W := mkw 0xb6d21f90fb71ff1e 0x05b690fc87db8ff8 0xfff01f80ffc1fc1b 0xefff80fc07fe0fe0

def z1226 : W := mkw 0xb7d45fef5b41bc18 0x15bea2ff7ada0de0 0xfffe7fffffc1fc1f 0xfffff3fffffe0fe0

def z1227 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fffffff01de3def 0xfbfffffff80ef1ef

def z1228 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x0000078000003c00 0x0000003c000001e0

def z1229 : W := mkw 0x7e49144800000000 0x13f248a240000000 0x5c0f9e7c0000000d 0xd2e07cf3e0000000

def z1230 : W := mkw 0x8c0914485b41bc18 0x046048a242da0de0 0xdc0f9e7cffc1fc1d 0xfee07cf3e7fe0fe0

def z1231 : W := mkw 0x5b6fe000e9300000 0x02db7f0007498000 0x7fffe000fff80017 0xebffff0007ffc000

def z1232 : W := mkw 0x534440004d040000 0x0a9a220002682000 0x7ff00000ffc00013 0xebff800007fe0000

def z1233 : W := mkw 0x1260a00049000000 0x0093050002480000 0x7ff1e000ffc00017 0xebff8f0007fe0000

def z1234 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0e1e7c00000008 0x92e070f3e0000000

def z1235 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x5c7fffff0000000d 0x12e3fffff8000000

def z1236 : W := mkw 0x7f7df6cd00000000 0x13fbefb668000000 0x7ffffe7c0000000f 0xd3fffff3e0000000

def z1237 : W := mkw 0x7ffdffef00401410 0x13ffefff780200a0 0xffffffff00003c0f 0xd7fffffff80001e0

def z1238 : W := mkw 0x0402141090216204 0x002010a084810b10 0xdc0f9e7cf039f39d 0xf6e07cf3e781cf9c

def z1239 : W := mkw 0x492fe07fa4be4306 0x1a497f03fd25f218 0x000fe07f003e0384 0x10007f03f801f01c

def z1240 : W := mkw 0x7ffdffef69da14b0 0x9bffefff7b4ed0a5 0x7fffffff71d8318f 0xf3fffffffb8ec18c

def z1241 : W := mkw 0xfffdffef5b01a808 0x17ffefff7ad80d40 0xfffffffffe01cc1f 0xdffffffffff00e60

def z1242 : W := mkw 0x7bfdeba700000000 0x13dfef5d38000000 0x7ffff9f30000000f 0xd3ffffcf98000000

def z1243 : W := mkw 0x0106403284244245 0x0008320194212212 0x0000600300260260 0x0000030018013013

def z1244 : W := mkw 0x0022a01586aecae5 0x80011500ac357657 0x8001e00f8e3fcff4 0x1c000f007c71fe7f

def z1245 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0x7fffffffffc1cc0f 0xdbfffffffffe0e60

def z1246 : W := mkw 0x5b6fe022edbe0000 0x0adb7f01176df000 0x7fffe073fffe0017 0xfbffff039ffff000

def z1247 : W := mkw 0x000200108624ca45 0x0000100084312652 0xa38000008e27ce72 0xcd1c000004713e73

def z1248 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01f80ffc1fc09 0xa7ff80fc07fe0fe0

def z1249 : W := mkw 0x493de2ef00ca14b0 0x9249ef17780650a5 0x007fe1ff01c60c66 0x1803ff0ff80e3063

def z1250 : W := mkw 0x7ffdffef10012000 0x13ffefff78800900 0xfffffffff039f39f 0xf7ffffffff81cf9c

def z1251 : W := mkw 0x018649328624ca45 0x000c324994312652 0xff8e79f3fe27ce7f 0xfffc73cf9ff13e73

def z1252 : W := mkw 0x80020010db61fe1c 0x0400100086db0ff0 0x80000000ffe1fe10 0x2c00000007ff0ff0

def z1253 : W := mkw 0x7ffdffef008a0000 0x13ffefff78045000 0x7fffffff01d8000f 0xf3fffffff80ec000

def z1254 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071e78f01fe3fed 0x34038f3c780ff1ff

def z1255 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80000600f039f399 0x640000300781cf9c

def z1256 : W := mkw 0x492de04800000000 0x02496f0240000000 0x000fe07c00000004 0x10007f03e0000000

def z1257 : W := mkw 0x00020010edbe4306 0x08001000876df218 0x00000000fffe0390 0x2800000007fff01c

def z1258 : W := mkw 0x4d0d546a00000000 0x12686aa350000000 0x5c0e187000000000 0x82e070c380000000

def z1259 : W := mkw 0x7ffdffef4d8e0000 0x1bffefff7a6c7000 0x7fffffff0ffe001f 0xfbfffffff87ff000

def z1260 : W := mkw 0x0080090000000000 0x0004004800000000 0x238e19f00000000e 0xd11c70cf80000000

def z1261 : W := mkw 0x13464032cd244245 0x009a320196692212 0x7ffe6073ffe60277 0xfbfff3039fff3013

def z1262 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff8001c01f 0xd7fffffffc000e00

def z1263 : W := mkw 0x00020010a0304306 0x0000100085018218 0x0001800c00380384 0x10000c006001c01c

def z1264 : W := mkw 0x00020010a4344347 0x000010008521a21a 0x00000000003e03e0 0x000000000001f01f

def z1265 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9e7cf019f199 0xe6e07cf3e780cf8c

def z1266 : W := mkw 0x5b4f4000ed340000 0x0ada7a000769a000 0x7ffe6000ffe60017 0xebfff30007ff3000

def z1267 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x00000000f019f180 0x200000000780cf8c

def z1268 : W := mkw 0x0002001084244245 0x0000100084212212 0x8000618300260e7e 0x5c00030c18013073

def z1269 : W := mkw 0xbadb0bd8eb70df1e 0x05d6d85ec75b86f8 0x23ff81fc0ff80f86 0x191ffc0fe07fc07c

def z1270 : W := mkw 0xb6d01fa25b41bc18 0x05b680fd12da0de0 0xfff01ff3ffc1fc1b 0xffff80ff9ffe0fe0

def z1271 : W := mkw 0xffcd5d6a5b01a808 0x17fe6aeb52d80d40 0xff8e79f3fe01cc1e 0xdffc73cf9ff00e60

def z1272 : W := mkw 0x0c1916cd004014b0 0x8060c8b6680200a5 0xdc0f9fff00003fed 0xd6e07cfff80001ff

def z1273 : W := mkw 0x73f4eba700000000 0x139fa75d38000000 0x23fe61f300000006 0x111ff30f98000000

def z1274 : W := mkw 0x00020010cf24ca45 0x0000100086792652 0x80000000ffe7ce70 0x2c00000007ff3e73

def z1275 : W := mkw 0x5b4d400049000000 0x02da6a0002480000 0x7ffe0000ffc00013 0xebfff00007fe0000

def z1276 : W := mkw 0xb6c01d005b01a808 0x05b600e802d80d40 0x7ff01800ffc1c001 0xa3ff80c007fe0e00

def z1277 : W := mkw 0x01b4eba706ce9cf1 0x800da75d383674e7 0xa3ffffff0ffe3fff 0xfd1ffffff87ff1ff

def z1278 : W := mkw 0xb7d45fa25f45bc59 0x05bea2fd12fa2de2 0xfffe7ff3ffc7fc7f 0xfffff3ff9ffe3fe3

def z1279 : W := mkw 0x492fe07fa4be4245 0x1a497f03fd25f212 0x000fe07f003e0264 0x10007f03f801f013

def z1280 : W := mkw 0x5f4d544800000000 0x02fa6aa240000000 0x7f8f9e7c0000000d 0xd3fc7cf3e0000000

def z1281 : W := mkw 0x1a49000069100000 0x00d2480003488000 0x7ff18000ffd80013 0xebff8c0007fec000

def z1282 : W := mkw 0x3fdd5fea00000000 0x01feeaff50000000 0x7fffffff0000000f 0xd3fffffff8000000

def z1283 : W := mkw 0x7fedfd6f00000000 0x13ff6feb78000000 0x7f8f987c00000000 0x83fc7cc3e0000000

def z1284 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e61f300000006 0x111c730f98000000

def z1285 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff0038001f 0xf3fffffff801c000

def z1286 : W := mkw 0x7ffdffc800000000 0x03ffeffe40000000 0x7ffffffc0000000f 0xd3ffffffe0000000

def z1287 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x23ffffff0000000e 0x111ffffff8000000

def z1288 : W := mkw 0x5b6de06f00000000 0x12db6f0378000000 0x7f8fe07f00000004 0x93fc7f03f8000000

def z1289 : W := mkw 0x25b4ffef00ca14b0 0x912da7ff780650a5 0xa3ffffff01fe3fff 0xfd1ffffff80ff1ff

def z1290 : W := mkw 0x00020010a4be4306 0x080010008525f218 0x00000000003e0380 0x000000000001f01c

def z1291 : W := mkw 0x04021410b0316306 0x002010a085818b18 0x80001e00f039f398 0x240000f00781cf9c

def z1292 : W := mkw 0xb3d44ba24b409c18 0x059ea25d125a04e0 0x23fe79f30fc00c0e 0xd91ff3cf987e0060

def z1293 : W := mkw 0x7fcd5d6a49000000 0x13fe6aeb52480000 0x7f8e1870fe000000 0x83fc70c387f00000

def z1294 : W := mkw 0x24901fef00000000 0x112480ff78000000 0x000e1fff0000000c 0xd00070fff8000000

def z1295 : W := mkw 0xa5945fa21241bc18 0x052ca2fd10920de0 0xa38e7ff30001fc0e 0xd51c73ff98000fe0

def z1296 : W := mkw 0xa4901fd81241ff1e 0x052480fec0920ff8 0x80001ff00001fc08 0x040000ff80000fe0

def z1297 : W := mkw 0x0184492200000000 0x000c224910000000 0xa38e79f300000e6e 0xd51c73cf98000073

def z1298 : W := mkw 0xfffdffef10413418 0x17ffefff788209a0 0x7fffffff0000300f 0xd3fffffff8000180

def z1299 : W := mkw 0x5b6de0006d9e0000 0x0adb6f00036cf000 0x7ff060007fc60002 0x0bff830003fe3000

def z1300 : W := mkw 0x493de2ef00ca14b0 0x9249ef17780650a5 0x007fe67f01d83185 0x3003ff33f80ec18c

def z1301 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e79f30e27ce6e 0x1d1c73cf98713e73

def z1302 : W := mkw 0x04021410b0316306 0x002010a085818b18 0xdc001800f039f390 0xa6e000c00781cf9c

def z1303 : W := mkw 0x5b7de2ef00000000 0x12dbef1778000000 0x7fffe7ff0000000f 0xd3ffff3ff8000000

def z1304 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff01f80ffc1fc03 0xabff80fc07fe0fe0

def z1305 : W := mkw 0x00020010a4be4245 0x080010008525f212 0x00000000003e0260 0x000000000001f013

def z1306 : W := mkw 0x12400000498a0000 0x00920000024c5000 0x7ff00000fffe0013 0xebff800007fff000

def z1307 : W := mkw 0x21944ba700000000 0x110ca25d38000000 0x238e79f30000000e 0xd11c73cf98000000

def z1308 : W := mkw 0x000200108664def5 0x80001000843326f7 0x800000008e27fff0 0x0c00000004713fff

def z1309 : W := mkw 0x7ef9bfcd00000000 0x13f7cdfe68000000 0x7fff9ffc0000000f 0xd3fffcffe0000000

def z1310 : W := mkw 0x5b6de0006d9e0000 0x0adb6f00036cf000 0x7ff1e0007ffe0017 0x6bff8f0003fff000

def z1311 : W := mkw 0x5b6fe058edbe4306 0x0adb7f02c76df218 0x7fffe070fffe0017 0xebffff0387fff000

def z1312 : W := mkw 0x6d8d5d6a00000000 0x136c6aeb50000000 0x000e187000000000 0x000070c380000000

def z1313 : W := mkw 0x7ffdffef00401410 0x13ffefff780200a0 0x7fffffff01c00c0f 0xdbfffffff80e0060

def z1314 : W := mkw 0x5b6de06a00000000 0x12db6f0350000000 0x7fffe07000000007 0xc3ffff0380000000

def z1315 : W := mkw 0xbec91d485b01a808 0x05f648ea42d80d40 0x7f8f9e7cfe01c00d 0xd3fc7cf3e7f00e00

def z1316 : W := mkw 0x1240000049000000 0x0092000002480000 0xfff00600ffc0301b 0xefff803007fe0180

def z1317 : W := mkw 0x0002001080204204 0x0000100084010210 0x800018008021c218 0xc40000c004010e10

def z1318 : W := mkw 0x69bdebef00000000 0x134def5f78000000 0x000fe1ff00000004 0x10007f0ff8000000

def z1319 : W := mkw 0x49ade96f00000000 0x124d6f4b78000000 0x238fe1ff00000006 0x111c7f0ff8000000

def z1320 : W := mkw 0xbed91fef5b41bc18 0x15f6c8ff7ada0de0 0xffff9fffffc1fc1f 0xfffffcfffffe0fe0

def z1321 : W := mkw 0x0002001090216204 0x0000100084810b10 0x80000000f021f210 0x2400000007810f90

def z1322 : W := mkw 0x7bfdebef00ca14b0 0x93dfef5f780650a5 0xa3ffe7ff01fe3fff 0x7d1fff3ff80ff1ff

def z1323 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238000008e01c000 0x011c000004700e00

def z1324 : W := mkw 0x0184492200000000 0x000c224910000000 0x238fffff0000000f 0xd11c7ffff8000000

def z1325 : W := mkw 0x492de06f209a0000 0x1a496f037904d000 0x000fe07f00180004 0x10007f03f800c000

def z1326 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01f8cffc1ff9b 0xffff80fc67fe0ffc

def z1327 : W := mkw 0x01944ba700000000 0x000ca25d38000000 0x238e7fff0000000e 0xd11c73fff8000000

def z1328 : W := mkw 0x00020010edbe4204 0x08001000876df210 0x80000000ffffc210 0x2c00000007fffe10

def z1329 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffe187000000000 0x83fff0c380000000

def z1330 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c01860cf019f181 0x22e00c306780cf8c

def z1331 : W := mkw 0x7ffdffef008a0000 0x13ffefff78045000 0x7fffffff01c6000f 0xdbfffffff80e3000

def z1332 : W := mkw 0x5b6de04800000000 0x02db6f0240000000 0x7fffe07c00000007 0xd3ffff03e0000000

def z1333 : W := mkw 0x0002001080204204 0x0000100084010210 0x8001860c8039f39d 0x74000c306401cf9c

def z1334 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff0026026f 0xd3fffffff8013013

def z1335 : W := mkw 0x37f4ffa700000000 0x01bfa7fd38000000 0x7fffffff0000000f 0xd3fffffff8000000

def z1336 : W := mkw 0x49ade96f02008800 0x124d6f4b78100440 0xa38ff9ff8e01cc1e 0xdd1c7fcffc700e60

def z1337 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e79f300000002 0x811c73cf98000000

def z1338 : W := mkw 0x498d496a00000000 0x124c6a4b50000000 0x238e79f30000000e 0xd11c73cf98000000

def z1339 : W := mkw 0x0c39b6cd10cb34b0 0x8061cdb6688659a5 0xdc7ffffff1ffffff 0xfee3ffffff8fffff

def z1340 : W := mkw 0x7fedfd6a00000000 0x13ff6feb50000000 0x7ffffe7c0000000f 0xd3fffff3e0000000

def z1341 : W := mkw 0x800200109665fe5d 0x0400100084b32ff2 0x800000008e27fe70 0x0c00000004713ff3

def z1342 : W := mkw 0x5b5f4285ed7414b0 0x8adafa142f6ba0a5 0xff8e078ffe003fe8 0x97fc703c7ff001ff

def z1343 : W := mkw 0x0400144800000000 0x002000a240000000 0x000e1e7c0000000c 0xd00070f3e0000000

def z1344 : W := mkw 0x0104402200000000 0x0008220110000000 0x238e607300000006 0xd11c730398000000

def z1345 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x0000000070383380 0x200000000381c19c

def z1346 : W := mkw 0x05845d2200000000 0x002c22e910000000 0x7f8e7ff30000000f 0xd3fc73ff98000000

def z1347 : W := mkw 0x7fedfd6a008a0000 0x13ff6feb50045000 0x7ffff87001fe0017 0xebffffc3800ff000

def z1348 : W := mkw 0x7fdd5fea00401410 0x13feeaff500200a0 0xfffe1ff001c03c1b 0xeffff0ff800e01e0

def z1349 : W := mkw 0x1240000059012000 0x0092000002c80900 0xfff00000ffc1f013 0xefff800007fe0f80

def z1350 : W := mkw 0x0022a010fdbf6306 0x0801150087edfb18 0x8071e60cfffff39f 0x7c038f3067ffff9c

def z1351 : W := mkw 0x1a49000049000000 0x00d2480002480000 0x7fff8000ffc00017 0xebfffc0007fe0000

def z1352 : W := mkw 0x3ef9bfcd00ca14b0 0x81f7cdfe680650a5 0xffffffff01fe3fff 0xfffffffff80ff1ff

def z1353 : W := mkw 0x0c09144800000000 0x006048a240000000 0xdc0f9e7c8001c01d 0xd6e07cf3e4000e00

def z1354 : W := mkw 0x0d8d5d6a00000000 0x006c6aeb50000000 0x7f8e79f30000000e 0xd3fc73cf98000000

def z1355 : W := mkw 0x01944ba200000000 0x000ca25d10000000 0x23fe7ff30000000f 0xd11ff3ff98000000

def z1356 : W := mkw 0xb6d01fa25b41bc59 0x05b680fd12da0de2 0xfff01f83ffc1fc7b 0xefff80fc1ffe0fe3

def z1357 : W := mkw 0x018449320604ca45 0x000c224990302652 0xa38e79f30e07ce6e 0xdd1c73cf98703e73

def z1358 : W := mkw 0x5bede92200000000 0x02df6f4910000000 0x7ffff87000000007 0xc3ffffc380000000

def z1359 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc01860cf039f39d 0x76e00c306781cf9c

def z1360 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffffffff000001f 0xf3ffffffff800000

def z1361 : W := mkw 0x0022a01086aeca45 0x0001150084357652 0x8071e0008fffce77 0x6c038f00047ffe73

def z1362 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fff8000fff80015 0xe3fffc0007ffc000

def z1363 : W := mkw 0x13c4492249000000 0x009e224912480000 0x7ffe79f3ffc0001f 0xfbfff3cf9ffe0000

def z1364 : W := mkw 0xb7d65fb2df65fe5d 0x05beb2fd96fb2ff2 0xfff07f83ffe7fe7b 0xefff83fc1fff3ff3

def z1365 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x000ff87f0000000c 0xd0007fc3f8000000

def z1366 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff0026001f 0xdbfffffff8013000

def z1367 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x000e607300000000 0x0000730398000000

def z1368 : W := mkw 0xfef9bfcd5b41bc18 0x17f7cdfe6ada0de0 0xffff9ffcffc1fc1f 0xfffffcffe7fe0fe0

def z1369 : W := mkw 0x1e49144800000000 0x00f248a240000000 0x7fff9e7c0000000f 0xd3fffcf3e0000000

def z1370 : W := mkw 0x01944ba200401410 0x000ca25d100200a0 0xa3fe7ff301c03c1f 0xfd1ff3ff980e01e0

def z1371 : W := mkw 0x7ffdffef02008800 0x13ffefff78100440 0xffffffff8e27ce7f 0xdffffffffc713e73

def z1372 : W := mkw 0xa5965fb29665fe5d 0x052cb2fd94b32ff2 0x800e7ff30027fe6c 0x140073ff98013ff3

def z1373 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071e78f01fe3fee 0x1c038f3c780ff1ff

def z1374 : W := mkw 0xa4901fdd1241ffbe 0x852480fee8920ffd 0x80001fff0001ffe8 0x140000fff8000fff

def z1375 : W := mkw 0xfffdffef5bcbbcb8 0x97ffefff7ade5de5 0xffffffffffc7fc7f 0xfffffffffffe3fe3

def z1376 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800001808e27ce7a 0x4c00000c04713e73

def z1377 : W := mkw 0x80020010dfeffefd 0x8400100086ff7ff7 0x80000000fffffff0 0x2c00000007ffffff

def z1378 : W := mkw 0x0c3bb6ddb0fb77b6 0x8061ddb6ed87dbbd 0xdc71e78ff1ffffff 0x7ee38f3c7f8fffff

def z1379 : W := mkw 0xfffdffef4bca9cb8 0x97ffefff7a5e54e5 0x7fffffff0fc60c6f 0xdbfffffff87e3063

def z1380 : W := mkw 0xb7d45fa259413418 0x05bea2fd12ca09a0 0x7ffe7ff371c0300f 0xf3fff3ff9b8e0180

def z1381 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x000019800001cc00 0x000000cc00000e60

def z1382 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800000008e01ce60 0x0400000004700e73

def z1383 : W := mkw 0x492de06f04040041 0x12496f0378202002 0x000fe07f00060064 0x10007f03f8003003

def z1384 : W := mkw 0x0c39b6cd30db35b2 0x8061cdb66986d9ad 0x5c7fffff71d8318f 0xf2e3fffffb8ec18c

def z1385 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x000fe67f0000000d 0x50007f33f8000000

def z1386 : W := mkw 0x5b6fe05dedbe43a6 0x8adb7f02ef6df21d 0x7fffe07ffffe03f7 0xfbffff03fffff01f

def z1387 : W := mkw 0x2c991fef00000000 0x1164c8ff78000000 0x5c0e1fff00000008 0x92e070fff8000000

def z1388 : W := mkw 0xfffdffef5bcbbc18 0x17ffefff7ade5de0 0xfffffffffffffc1f 0xffffffffffffffe0

def z1389 : W := mkw 0x41a4e92700000000 0x120d274938000000 0x238e79f30000000e 0xd11c73cf98000000

def z1390 : W := mkw 0x5a6ba010efbeca45 0x0ad35d00877df652 0xdc718000ffffce71 0x2ee38c0007fffe73

def z1391 : W := mkw 0x24921fefedbe0000 0x192490ff7f6df000 0x00001ffffffe0018 0x380000fffffff000

def z1392 : W := mkw 0x5b7de2ef00ca14b0 0x92dbef17780650a5 0xffffe7ff01fe3fff 0xffffff3ff80ff1ff

def z1393 : W := mkw 0x00920b9086eedef5 0x8004905c843776f7 0xa3f01f808ffffffb 0xed1f80fc047fffff

def z1394 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xfffff800ffffc01f 0xefffffc007fffe00

def z1395 : W := mkw 0x37d45fa200000000 0x01bea2fd10000000 0x7ffe1ff00000000b 0xc3fff0ff80000000

def z1396 : W := mkw 0xb6d01f855b41bcb8 0x85b680fc2ada0de5 0xfff19f8ffff9ffff 0xffff8cfc7fffcfff

def z1397 : W := mkw 0x80020010fb31eb0e 0x0400100087d98f58 0x80000000fe39f390 0x2400000007f1cf9c

def z1398 : W := mkw 0xfffdffa25b41bc18 0x07ffeffd12da0de0 0xfffffff3ffc1fc1f 0xffffffff9ffe0fe0

def z1399 : W := mkw 0x0184492200000000 0x000c224910000000 0x000e79f30000000c 0x100073cf98000000

def z1400 : W := mkw 0x492fe032a4be4245 0x0a497f019525f212 0x000fe070003e0004 0x00007f038001f000

def z1401 : W := mkw 0x5366e000cdae0000 0x0a9b3700066d7000 0x7ffe6000ffe60017 0xebfff30007ff3000

def z1402 : W := mkw 0x5e6bb458fdbf6306 0x0af35da2c7edfb18 0xdc71860cfffff391 0x2ee38c3067ffff9c

def z1403 : W := mkw 0x7ffdffef30112102 0x13ffefff79808908 0x7fffffff7000000f 0xd3fffffffb800000

def z1404 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x00000000f039c010 0x200000000781ce00

def z1405 : W := mkw 0x7ffdffef1201a800 0x13ffefff78900d40 0xfffffffffe01fc1f 0xfffffffffff00fe0

def z1406 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x000f807c00000000 0x00007c03e0000000

def z1407 : W := mkw 0x7fedfd6a699a0000 0x1bff6feb534cd000 0x7fff987071d80001 0xa3fffcc3838ec000

def z1408 : W := mkw 0x0000000000000000 0x0000000000000000 0x800f9e7c0038339d 0xf4007cf3e001c19c

def z1409 : W := mkw 0x0c09144810012102 0x006048a240800908 0x5c0f9e7c0000318d 0xd2e07cf3e000018c

def z1410 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff01800ffc1c000 0x83ff80c007fe0e00

def z1411 : W := mkw 0xb7d45fa25b41bc18 0x05bea2fd12da0de0 0xfffe7ff3ffe7fe7f 0xfffff3ff9fff3ff3

def z1412 : W := mkw 0x0002001080204204 0x0000100084010210 0x800061838027ce7e 0x5c00030c1c013e73

def z1413 : W := mkw 0x1260a000498a0000 0x00930500024c5000 0x7ff18000ffd80013 0xebff8c0007fec000

def z1414 : W := mkw 0xfffdffef5b01a808 0x17ffefff7ad80d40 0x7fffffffffc1c01f 0xfbfffffffffe0e00

def z1415 : W := mkw 0x0184492202008800 0x000c224910100440 0x238e79f30e000c0e 0xd91c73cf98700060

def z1416 : W := mkw 0x5b6fe022edbe0041 0x0adb7f01176df002 0x7fffe003fffe0077 0xebffff001ffff003

def z1417 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e79f30026001e 0xd91c73cf98013000

def z1418 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffe7ff00000007 0x13ffff3ff8000000

def z1419 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e79f38e00001e 0xd91c73cf9c700000

def z1420 : W := mkw 0xb6d01f805b01a808 0x05b680fc02d80d40 0x7ff01f80ffc1c01b 0xebff80fc07fe0e00

def z1421 : W := mkw 0x7ffdffef69100000 0x1bffefff7b488000 0x7fffffff7000000f 0xd3fffffffb800000

def z1422 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe0007ffe0007 0x2bffff0003fff000

def z1423 : W := mkw 0x7fdd5fea00000000 0x13feeaff50000000 0x7fff9ffc0000000f 0xd3fffcffe0000000

def z1424 : W := mkw 0x36d01f804b008800 0x01b680fc02580440 0xfff01f80ffc1cc1b 0xefff80fc07fe0e60

def z1425 : W := mkw 0x0104406f00000000 0x1008220378000000 0x000e607f00000004 0x10007303f8000000

def z1426 : W := mkw 0x0002001084244245 0x0000100084212212 0x0000000000000000 0x0000000000000000

def z1427 : W := mkw 0x25945fef004014b0 0x912ca2ff780200a5 0xa38e7fff00263ffe 0xdd1c73fff80131ff

def z1428 : W := mkw 0xb3d64bb2df65fe5d 0x059eb25d96fb2ff2 0xa3f06183ffe7fe72 0x2d1f830c1fff3ff3

def z1429 : W := mkw 0x01b4eba700ca14b0 0x800da75d380650a5 0x23fe79f301c60c6e 0xd91ff3cf980e3063

def z1430 : W := mkw 0x7e79b6cd00ca14b0 0x93f3cdb6680650a5 0xdc7fffff01fe3fff 0xfee3fffff80ff1ff

def z1431 : W := mkw 0xb6d01fc85b41bd1a 0x05b680fe42da0de8 0xfff01f8cffc1fd9b 0xefff80fc67fe0fec

def z1432 : W := mkw 0x80020010ffffff1e 0x0c00100087fffff8 0x80000000ffffff90 0x2c00000007fffffc

def z1433 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff8e00001f 0xdbfffffffc700000

def z1434 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0x7ff01f80ffc1cc0b 0xcbff80fc07fe0e60

def z1435 : W := mkw 0x0104402200000000 0x0008220110000000 0x800e61f300260e7e 0x5c00730f98013073

def z1436 : W := mkw 0x1a6ba000e9ba0000 0x00d35d00074dd000 0x7fffe000fffe0017 0xebffff0007fff000

def z1437 : W := mkw 0x5b4f4000edbe0000 0x0ada7a00076df000 0x7ffe0000fffe0013 0xebfff00007fff000

def z1438 : W := mkw 0x25945fef00000000 0x112ca2ff78000000 0x000e7fff0000000c 0x100073fff8000000

def z1439 : W := mkw 0x7ffdffef10012000 0x13ffefff78800900 0x7ffffffff001c00f 0xd3ffffffff800e00

def z1440 : W := mkw 0x00020010b07177b6 0x8000100085838bbd 0x80000000f039fff0 0x240000000781cfff

def z1441 : W := mkw 0x124000004d8e0000 0x08920000026c7000 0x7ff00000ffc60013 0xebff800007fe3000

def z1442 : W := mkw 0x00020010a0304306 0x0000100085018218 0x00000000f0380390 0x200000000781c01c

def z1443 : W := mkw 0x4d2df44800000000 0x02696fa240000000 0x5c0ffe7c0000000d 0xd2e07ff3e0000000

def z1444 : W := mkw 0x0184492202008800 0x000c224910100440 0x238e18708e01c000 0x811c70c384700e00

def z1445 : W := mkw 0xfffdffef7951351a 0x17ffefff7bca89a8 0x7fffffff71d8318f 0xf3fffffffb8ec18c

def z1446 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc000000f039f390 0x26e000000781cf9c

def z1447 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff19f8cffd9fd9b 0xefff8cfc67fecfec

def z1448 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f9e7c0038038d 0xd2e07cf3e001c01c

def z1449 : W := mkw 0x0c0b1458b4356306 0x006058a2c5a1ab18 0xdc0f9e7cfe3ff39d 0xfee07cf3e7f1ff9c

def z1450 : W := mkw 0x7ffdffef20100102 0x13ffefff79008008 0x7fffffff0018018f 0xd3fffffff800c00c

def z1451 : W := mkw 0x49bdebef00ca14b0 0x924def5f780650a5 0xa3ffffff01fe3fff 0xfd1ffffff80ff1ff

def z1452 : W := mkw 0x00020010b635eb47 0x0000100085b1af5a 0x8001e78ffe3fffff 0x7c000f3c7ff1ffff

def z1453 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9e7cf03ffffd 0xfee07cf3e781ffff

def z1454 : W := mkw 0x7bede96f00000000 0x13df6f4b78000000 0x238fe07f00000004 0x111c7f03f8000000

def z1455 : W := mkw 0x0032a29580ea56b4 0x80019514ac0752b5 0x8071e78f81ffffff 0x7c038f3c7c0fffff

def z1456 : W := mkw 0xffedfd6f5b01a808 0x17ff6feb7ad80d40 0x7f8ff87ffe01c004 0x93fc7fc3fff00e00

def z1457 : W := mkw 0xb2d00b805b41bc18 0x0596805c02da0de0 0xfff00180ffc1fc13 0xefff800c07fe0fe0

def z1458 : W := mkw 0x0809000000000000 0x0040480000000000 0x5c0f98700000000d 0xd2e07cc380000000

def z1459 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x0071e78f01fe3fe7 0x38038f3c780ff1ff

def z1460 : W := mkw 0xbef9bfcd5bcbbcb8 0x85f7cdfe6ade5de5 0xffffffffffffffff 0xffffffffffffffff

def z1461 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffffe7f00000005 0x93fffff3f8000000

def z1462 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800000008e27ce7c 0x5c00000004713e73

def z1463 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e787000000006 0xc11c73c380000000

def z1464 : W := mkw 0xffdd5fea5b41bc18 0x17feeaff52da0de0 0xfffe7ff3ffc1fc1f 0xfffff3ff9ffe0fe0

def z1465 : W := mkw 0x0809004820100102 0x0040480241008008 0x000f807c00180184 0x10007c03e000c00c

def z1466 : W := mkw 0x5bcd492200000000 0x02de6a4910000000 0x7f8e79f30000000e 0xd3fc73cf98000000

def z1467 : W := mkw 0xb650168059413418 0x05b280b402ca09a0 0xfff01e00ffc1f01b 0xefff80f007fe0f80

def z1468 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e19f300000008 0x911c70cf98000000

def z1469 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0f9e7cf039f385 0xb2e07cf3e781cf9c

def z1470 : W := mkw 0x7ffdffef4f8e8841 0x1bffefff7a7c7442 0x7fffffff0fc60c6f 0xdbfffffff87e3063

def z1471 : W := mkw 0x0c09144830112102 0x006048a241808908 0x5c0f867c70183185 0x32e07c33e380c18c

def z1472 : W := mkw 0x5b4f4000ed340000 0x0ada7a000769a000 0x7ffe0000ffc00002 0x8bfff00007fe0000

def z1473 : W := mkw 0xfffdffef79db3418 0x1fffefff7bced9a0 0x7fffffff71d8300f 0xf3fffffffb8ec180

def z1474 : W := mkw 0x00020010fdff77b6 0x8800100087effbbd 0x80000000fffffff0 0x2c00000007ffffff

def z1475 : W := mkw 0xb6d21f90ff75ff5f 0x05b690fc87fbaffa 0xfff01f80fffffffb 0xefff80fc07ffffff

def z1476 : W := mkw 0x492fe037a4be42e5 0x8a497f01bd25f217 0x000fe07f003e03e4 0x10007f03f801f01f

def z1477 : W := mkw 0x0184492206048841 0x000c224910302442 0x238e18700e000000 0x811c70c380700000

def z1478 : W := mkw 0x0000000000000000 0x0000000000000000 0x000e007000000004 0x1000700380000000

def z1479 : W := mkw 0x25b4ffef00000000 0x112da7ff78000000 0x23ffffff0000000f 0xd11ffffff8000000

def z1480 : W := mkw 0xb6f2bf95dfeffefd 0x85b795fcaeff7ff7 0xfff1ff8fffffffff 0xffff8ffc7fffffff

def z1481 : W := mkw 0x0184492206048841 0x000c224910302442 0x238e61f30e060c66 0x191c730f98703063

def z1482 : W := mkw 0x00020010a634cb47 0x000010008531a65a 0x800000008e3fcff0 0x0c0000000471fe7f

def z1483 : W := mkw 0x5b4f4000ed340000 0x0ada7a000769a000 0x7fff8000fff80017 0xebfffc0007ffc000

def z1484 : W := mkw 0xbef9bfcd5b41bc18 0x05f7cdfe6ada0de0 0xffffffffffc1fc1f 0xfffffffffffe0fe0

def z1485 : W := mkw 0x7ffdffef06048841 0x13ffefff78302442 0xffffffff0e260e7f 0xdffffffff8713073

def z1486 : W := mkw 0x0c29b44d008a00a0 0x80614da268045005 0x5c0ffe7f003e03ed 0xd2e07ff3f801f01f

def z1487 : W := mkw 0x0000000000000000 0x0000000000000000 0x800e79f300260e7e 0xdc0073cf98013073

def z1488 : W := mkw 0x00020010edbe4245 0x08001000876df212 0x00000000fffe0270 0x2800000007fff013

def z1489 : W := mkw 0x0032a29584ee56f5 0x80019514ac2772b7 0x8071e78f01fe3fff 0x7c038f3c780ff1ff

def z1490 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f867c00000005 0x12e07c33e0000000

def z1491 : W := mkw 0x7ffdffef048e0000 0x1bffefff78247000 0x7fffffff0006000f 0xd3fffffff8003000

def z1492 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0x7fffffffffc1f00f 0xf3fffffffffe0f80

def z1493 : W := mkw 0xffdd5fef5b41bc18 0x17feeaff7ada0de0 0xfffe1fffffc1fc1b 0xfffff0fffffe0fe0

def z1494 : W := mkw 0x00020010b0316306 0x0000100085818b18 0xdc000000f039f391 0xe6e000000781cf9c

def z1495 : W := mkw 0x7ffdffef30db35b2 0x93ffefff7986d9ad 0xffffffff71fe3fff 0xfffffffffb8ff1ff

def z1496 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0xffffffff01d83fef 0xf7fffffff80ec1ff

def z1497 : W := mkw 0xa4901fa21241bc18 0x052480fd10920de0 0x80001ff30001fc08 0x140000ff98000fe0

def z1498 : W := mkw 0x5b6fe010edbe4204 0x0adb7f00876df210 0x7ffff870ffffc017 0xebffffc387fffe00

def z1499 : W := mkw 0x37c45d2200000000 0x01be22e910000000 0x7f8e79f30000000e 0xd3fc73cf98000000

def z1500 : W := mkw 0x0c09146f00000000 0x106048a378000000 0x5c0f9e7f0000000d 0xd2e07cf3f8000000

def z1501 : W := mkw 0x00020010a0fa57b6 0x800010008507d2bd 0x8000000001fe3ff0 0x2c000000000ff1ff

def z1502 : W := mkw 0x7fedfd6a4d8e0000 0x1bff6feb526c7000 0x7ffe78700fc60002 0x8bfff3c3807e3000

def z1503 : W := mkw 0x0c09144820100000 0x006048a241008000 0x5c0f9e7c7018000d 0xf2e07cf3e380c000

def z1504 : W := mkw 0x0022a015a0ba43a6 0x80011500ad05d21d 0x0001e00f003e03e4 0x10000f007801f01f

def z1505 : W := mkw 0x00020010b6fffff7 0x8000100085b7ffff 0x80000000fffffff0 0x2c00000007ffffff

def z1506 : W := mkw 0x00120295b07177b6 0x80009014ad838bbd 0x8000078ff039fff8 0x3400003c7f81cfff

def z1507 : W := mkw 0xfffdffef12cbbcb8 0x97ffefff78965de5 0xffffffff01ffffff 0xfffffffff80fffff

def z1508 : W := mkw 0xb6d21f90fffffe5d 0x0db690fc87fffff2 0xfff01f80fffffe7b 0xefff80fc07fffff3

def z1509 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe000fffe0005 0xa3ffff0007fff000

def z1510 : W := mkw 0x492de06a00000000 0x12496f0350000000 0x000fe07000000004 0x00007f0380000000

def z1511 : W := mkw 0xa4901ffa1241ff5f 0x052480ffd0920ffa 0x80001fff0001ffe8 0x140000fff8000fff

def z1512 : W := mkw 0x4dadfd6f00000000 0x126d6feb78000000 0x7f8fffff0000000f 0xd3fc7ffff8000000

def z1513 : W := mkw 0x77f4ffa700000000 0x13bfa7fd38000000 0x7ffe7ff30000000f 0xd3fff3ff98000000

def z1514 : W := mkw 0xffdd5fef5b41bc18 0x17feeaff7ada0de0 0xff8e1ffffe01fc08 0x97fc70fffff00fe0

def z1515 : W := mkw 0x925002805b41bc18 0x0492801402da0de0 0xfff00780ffc1fc1b 0xefff803c07fe0fe0

def z1516 : W := mkw 0x492de06f008a0000 0x12496f0378045000 0x000fe07f003e0004 0x10007f03f801f000

def z1517 : W := mkw 0xa5945fef1241bc18 0x152ca2ff78920de0 0xa38e7fff8e01fc1e 0xdd1c73fffc700fe0

def z1518 : W := mkw 0x0032a295b0316306 0x00019514ad818b18 0x8071e78ff039f39f 0x74038f3c7f81cf9c

def z1519 : W := mkw 0x0c39b6cd00000000 0x0061cdb668000000 0x5c7f9e7c0000000d 0xd2e3fcf3e0000000

def z1520 : W := mkw 0x0809004800000000 0x0040480240000000 0x800f867c0038339d 0x74007c33e001c19c

def z1521 : W := mkw 0x73f4eba700000000 0x139fa75d38000000 0x23ffffff0000000f 0xd11ffffff8000000

def z1522 : W := mkw 0x5e79b6cd79db35b2 0x8af3cdb66bced9ad 0x5c71860c71d83181 0x22e38c30638ec18c

def z1523 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0xffffffff01d83d9f 0xfffffffff80ec1ec

def z1524 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7ffe6000ffe60016 0xcbfff30007ff3000

def z1525 : W := mkw 0x7ffdffef10012000 0x13ffefff78800900 0xffffffff0001f00f 0xd7fffffff8000f80

def z1526 : W := mkw 0x5b6de00000000000 0x02db6f0000000000 0x7ffff8700000000f 0xd3ffffc380000000

def z1527 : W := mkw 0x7ffdffef004014b0 0x93ffefff780200a5 0xffffffff00383fff 0xf7fffffff801c1ff

def z1528 : W := mkw 0x7fedfd6f00000000 0x13ff6feb78000000 0x7f8ff9ff0000000e 0xd3fc7fcff8000000

def z1529 : W := mkw 0xfffdffef59413418 0x17ffefff7aca09a0 0x7fffffffffc0301f 0xfbfffffffffe0180

def z1530 : W := mkw 0x1344400049000000 0x009a220002480000 0x7ffe6000ffc00017 0xebfff30007fe0000

def z1531 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fff9ffc0000000b 0xc3fffcffe0000000

def z1532 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x8001800cf039f394 0x34000c006781cf9c

def z1533 : W := mkw 0x0022a010efbeca45 0x08011500877df652 0x8071e183ffffce7f 0x7c038f0c1ffffe73

def z1534 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0x7fffffff7fc03c0f 0xfbfffffffbfe01e0

def z1535 : W := mkw 0x0c09144800000000 0x006048a240000000 0xdc0f9e7c0020021d 0xd6e07cf3e0010010

def z1536 : W := mkw 0xffcd5d6a59012008 0x17fe6aeb52c80900 0x7f8e187070000000 0x83fc70c383800000

def z1537 : W := mkw 0x5b6fe010edbe4204 0x0adb7f00876df210 0xfffff9f3ffffce7f 0xffffffcf9ffffe73

def z1538 : W := mkw 0x37d45fef00000000 0x11bea2ff78000000 0x7ffe7fff0000000f 0xd3fff3fff8000000

def z1539 : W := mkw 0x0184492204040000 0x000c224910202000 0x238e79f30e06000e 0xd91c73cf98703000

def z1540 : W := mkw 0x7ffdffef10cb34b0 0x93ffefff788659a5 0xfffffffff1ffffff 0xffffffffff8fffff

def z1541 : W := mkw 0x492fe010a4be4306 0x0a497f008525f218 0x000fe000003e0384 0x00007f000001f01c

def z1542 : W := mkw 0xfe79b6cd59413418 0x17f3cdb66aca09a0 0xdc7f9e7cf1c1f01d 0xf6e3fcf3e78e0f80

def z1543 : W := mkw 0x0134e2a700ca14b0 0x8009a715380650a5 0x807fe7ff01fe3fff 0x7c03ff3ff80ff1ff

def z1544 : W := mkw 0x7ffdffef008a00a0 0x93ffefff78045005 0xffffffff003e33ff 0xf7fffffff801f19f

def z1545 : W := mkw 0x0032a295b6fffff7 0x80019514adb7ffff 0x8071e78fffffffff 0x7c038f3c7fffffff

def z1546 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9e7cf039f38c 0x96e07cf3e781cf9c

def z1547 : W := mkw 0x3ef9bfcd00000000 0x01f7cdfe68000000 0x7fffffff0000000f 0xd3fffffff8000000

def z1548 : W := mkw 0xbed91fc85b41bc18 0x05f6c8fe42da0de0 0xfffe1ff0ffc1fc1b 0xeffff0ff87fe0fe0

def z1549 : W := mkw 0x0124e02700000000 0x0009270138000000 0x000fe07f00000004 0x10007f03f8000000

def z1550 : W := mkw 0xa4901f901241ff1e 0x052480fc80920ff8 0x80001f800001ff88 0x040000fc00000ffc

def z1551 : W := mkw 0x5e69b44800000000 0x02f34da240000000 0x5c7f9e7c0000000d 0xd2e3fcf3e0000000

def z1552 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e79f38e27ce66 0x991c73cf9c713e73

def z1553 : W := mkw 0x492de06f008a00a0 0x92496f0378045005 0x000fe07f00180184 0x10007f03f800c00c

def z1554 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01e00ffc1fc11 0xafff80f007fe0fe0

def z1555 : W := mkw 0x0002001086aeca45 0x0000100084357652 0x800000008fffce70 0x2c000000047ffe73

def z1556 : W := mkw 0x000200108664de55 0x00001000843326f2 0x800000008fe7fe70 0x2c000000047f3ff3

def z1557 : W := mkw 0x00020010b4bf6306 0x0800100085a5fb18 0x80000000f03ff390 0x240000000781ff9c

def z1558 : W := mkw 0x80020010df25ea4d 0x0400100086f92f52 0x80000000fe27ce70 0x0c00000007f13e73

def z1559 : W := mkw 0x7ffdffef49000000 0x13ffefff7a480000 0x7fffffff71c0000f 0xf3fffffffb8e0000

def z1560 : W := mkw 0x1650168059413410 0x00b280b402ca09a0 0xfff01f80ffc1fc1b 0xefff80fc07fe0fe0

def z1561 : W := mkw 0x1260a005498a00a0 0x809305002a4c5005 0x7ff1e00ffffe03f7 0xfbff8f007ffff01f

def z1562 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01f80ffc1fc0a 0x8fff80fc07fe0fe0

def z1563 : W := mkw 0x0c29b44800000000 0x00614da240000000 0x5c7ffe7c0000000f 0xd2e3fff3e0000000

def z1564 : W := mkw 0xfffdffef59012008 0x17ffefff7ac80900 0x7fffffff7000000f 0xd3fffffffb800000

def z1565 : W := mkw 0x7fedfd6a00000000 0x13ff6feb50000000 0x7f8ff87000000004 0x83fc7fc380000000

def z1566 : W := mkw 0x7ffdffef02008800 0x13ffefff78100440 0x7fffffff8e01c00f 0xd3fffffffc700e00

def z1567 : W := mkw 0x0134e2a700000000 0x0009a71538000000 0x007fe7ff0000000f 0x5003ff3ff8000000

def z1568 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffe79f30000000e 0xd3fff3cf98000000

def z1569 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238061830e260e62 0x091c030c18713073

def z1570 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xffffe180fffe0c1f 0xefffff0c07fff060

def z1571 : W := mkw 0xb3f4eba74fce9cf9 0x859fa75d3a7e74e7 0x23f061830fc60c62 0x091f830c187e3063

def z1572 : W := mkw 0x53f4eba74fce9cf1 0x8a9fa75d3a7e74e7 0x23f061830fc60c62 0x091f830c187e3063

def z1573 : W := mkw 0x0002001080204204 0x0000100084010210 0x000000008001c000 0x0000000004000e00

def z1574 : W := mkw 0xa4901f851241bcb8 0x852480fc28920de5 0x80001f830001fc68 0x040000fc18000fe3

def z1575 : W := mkw 0x0184492202008800 0x000c224910100440 0x238e79f38e01c00e 0xd11c73cf9c700e00

def z1576 : W := mkw 0xb6c01d005b01a808 0x05b600e802d80d40 0x7ff01800ffc1c002 0x8bff80c007fe0e00

def z1577 : W := mkw 0x7e79b6cd00000000 0x13f3cdb668000000 0x5c7f9e7c00000001 0x82e3fcf3e0000000

def z1578 : W := mkw 0x7bfdebef00000000 0x13dfef5f78000000 0x23fff9ff0000000e 0xd11fffcff8000000

def z1579 : W := mkw 0x0184492200000000 0x000c224910000000 0xa38fffff0038339f 0xf51c7ffff801c19c

def z1580 : W := mkw 0xfffdffef5b41bcb8 0x97ffefff7ada0de5 0xffffffffffc1ffff 0xfffffffffffe0fff

def z1581 : W := mkw 0x5f6df448008a0000 0x02fb6fa240045000 0xfffffe7c01fe339f 0xfffffff3e00ff19c

def z1582 : W := mkw 0x0080092200000000 0x0004004910000000 0x000e19f30000000c 0xd00070cf98000000

def z1583 : W := mkw 0x010640328624ca45 0x0008320194312652 0x800060038e27ce70 0x0c0003001c713e73

def z1584 : W := mkw 0x01b4eba702409c10 0x000da75d381204e0 0xa3ffffff8fc1fc1f 0xfd1ffffffc7e0fe0

def z1585 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0xffffffffffe7fe7f 0xffffffffffff3ff3

def z1586 : W := mkw 0x01864932b635eb47 0x000c324995b1af5a 0xa3806183fe3ffff2 0x2d1c030c1ff1ffff

def z1587 : W := mkw 0x80020010fb31eb0e 0x0400100087d98f58 0x00000000fe01c000 0x0000000007f00e00

def z1588 : W := mkw 0x0032a2958624ca45 0x00019514ac312652 0x8071e78f8e27ce7f 0x5c038f3c7c713e73

def z1589 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38000008e27ce70 0x0d1c000004713e73

def z1590 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800000008e3ffff0 0x2c0000000471ffff

def z1591 : W := mkw 0x00020010cfaeca45 0x08001000867d7652 0x800000008fe7ce70 0x0c000000047f3e73

def z1592 : W := mkw 0x01b6ebb786eedef5 0x800db75dbc3776f7 0xa3f1e78f8fffffff 0x7d1f8f3c7c7fffff

def z1593 : W := mkw 0x04901f801241bc10 0x002480fc00920de0 0xfff01f80ffc1fc1b 0xefff80fc07fe0fe0

def z1594 : W := mkw 0x5b6fe058edbe4306 0x0adb7f02c76df218 0xffffe67cfffe339f 0xffffff33e7fff19c

def z1595 : W := mkw 0x25845d6a00000000 0x112c22eb50000000 0x238e187000000000 0x811c70c380000000

def z1596 : W := mkw 0x0080090002008800 0x0004004800100440 0xa38e19f08e01cc1e 0xdd1c70cf84700e60

def z1597 : W := mkw 0x7ffdffef004014b0 0x93ffefff780200a5 0xffffffff00263fff 0xdffffffff80131ff

def z1598 : W := mkw 0xfffdffef4fce9c18 0x1fffefff7a7e74e0 0x7fffffff0fc60c0f 0xdbfffffff87e3060

def z1599 : W := mkw 0xfffdffef1241bc18 0x17ffefff78920de0 0xffffffff8e01fc1f 0xdffffffffc700fe0

def z1600 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80001800f039f398 0xe40000c00781cf9c

def z1601 : W := mkw 0xa4901f801241bcb8 0x852480fc00920de5 0x80001f800001ffe8 0x040000fc00000fff

def z1602 : W := mkw 0x7ffdffef498a0000 0x1bffefff7a4c5000 0x7fffffff01c0000f 0xd3fffffff80e0000

def z1603 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff07f83ffc1fc1f 0xffff83fc1ffe0fe0

def z1604 : W := mkw 0x0022a010b0bb6306 0x000115008585db18 0x8071e000f1fff397 0x6c038f00078fff9c

def z1605 : W := mkw 0xfffdffef4b409c18 0x17ffefff7a5a04e0 0x7fffffffffc00c1f 0xfbfffffffffe0060

def z1606 : W := mkw 0x3ed91fc800000000 0x01f6c8fe40000000 0x7ffe1ff00000000b 0xc3fff0ff80000000

def z1607 : W := mkw 0x0184492206048841 0x000c224910302442 0x238e79f30e00000e 0xd11c73cf98700000

def z1608 : W := mkw 0x7ffdffef04040000 0x13ffefff78202000 0x7fffffff0e06000f 0xdbfffffff8703000

def z1609 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fff8000fffe0011 0xabfffc0007fff000

def z1610 : W := mkw 0x008209108624ca45 0x0004104884312652 0x800019808e27ce78 0x0c0000cc04713e73

def z1611 : W := mkw 0x0c09144800000000 0x006048a240000000 0xdc0fffff00260e7f 0xdee07ffff8013073

def z1612 : W := mkw 0x5e69b448699a0000 0x0af34da2434cd000 0x5c7f9e7c71d8000d 0xf2e3fcf3e38ec000

def z1613 : W := mkw 0x7fdd5fea00000000 0x13feeaff50000000 0x7f8e1ff000000008 0x83fc70ff80000000

def z1614 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fff9fff00000009 0x93fffcfff8000000

def z1615 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x800fe1ff00260e7e 0x5c007f0ff8013073

def z1616 : W := mkw 0x7ffdffef008a0000 0x13ffefff78045000 0xffffffff01fe339f 0xfffffffff80ff19c

def z1617 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fff9e7c0000000d 0xd3fffcf3e0000000

def z1618 : W := mkw 0x001202908664de55 0x00009014843326f2 0x807007808fe7fe7b 0x6c03803c047f3ff3

def z1619 : W := mkw 0x2c991fef004014b0 0x9164c8ff780200a5 0xdc0f9fff00383ffd 0xf6e07cfff801c1ff

def z1620 : W := mkw 0x0002001080204204 0x0000100084010210 0x800000008021c21c 0x5400000004010e10

def z1621 : W := mkw 0x5b6fe005edbe00a0 0x8adb7f002f6df005 0x7fffe00cfffe0197 0xebffff0067fff00c

def z1622 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38ff9ff8e3fcffe 0xdd1c7fcffc71fe7f

def z1623 : W := mkw 0xbe79b6cd79db35ba 0x85f3cdb66bced9ad 0x5c71860c71d83181 0x22e38c30638ec18c

def z1624 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff0020021f 0xd7fffffff8010010

def z1625 : W := mkw 0x5fcf5d7aff35eb47 0x0afe7aebd7f9af5a 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z1626 : W := mkw 0x7fcd5d6a30112102 0x13fe6aeb51808908 0x7f8e187070000000 0x83fc70c383800000

def z1627 : W := mkw 0x7e79b6cd00000000 0x13f3cdb668000000 0x5c7f867c00000005 0x12e3fc33e0000000

def z1628 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80000000f001f380 0x0400000007800f9c

def z1629 : W := mkw 0x1240000049000000 0x0092000002480000 0xfff1860cfff8339f 0xffff8c3067ffc19c

def z1630 : W := mkw 0xb6d01f855b41bc18 0x05b680fc2ada0de0 0xfff01f8fffc1fc1b 0xffff80fc7ffe0fe0

def z1631 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800061838e27ce72 0x0c00030c1c713e73

def z1632 : W := mkw 0xb6d01fa75b41bc18 0x15b680fd3ada0de0 0xfff01f83ffc1fc1b 0xefff80fc1ffe0fe0

def z1633 : W := mkw 0x0002001084244245 0x0000100084212212 0x8000000000260e70 0x0c00000000013073

def z1634 : W := mkw 0xbfcf5d7aff35eb4f 0x05fe7aebd7f9af5a 0x7f8e1870fe01c000 0x83fc70c387f00e00

def z1635 : W := mkw 0x2cb9bfef00ca14b0 0x9165cdff780650a5 0xdc7fffff01fe3fff 0xfee3fffff80ff1ff

def z1636 : W := mkw 0xb7f4ffa75b41bc18 0x05bfa7fd3ada0de0 0xffffffffffc1fc1f 0xfffffffffffe0fe0

def z1637 : W := mkw 0x7ffdffef4d8e0000 0x1bffefff7a6c7000 0x7fffffffffc6001f 0xfbfffffffffe3000

def z1638 : W := mkw 0xfffdffef5f45bc59 0x17ffefff7afa2de2 0xffffffffffc7fc7f 0xfffffffffffe3fe3

def z1639 : W := mkw 0x33d44ba200000000 0x019ea25d10000000 0x23fe79f30000000e 0xd11ff3cf98000000

def z1640 : W := mkw 0xfffdffef1241bc18 0x17ffefff78920de0 0xffffffff01c1fc1f 0xfffffffff80e0fe0

def z1641 : W := mkw 0x5364e0004d8e0000 0x0a9b2700026c7000 0x7ff06000ffc60002 0x8bff830007fe3000

def z1642 : W := mkw 0xb6521690f971771e 0x05b290b487cb8bb8 0xdc700600f1f9f391 0x26e38030078fcf9c

def z1643 : W := mkw 0x0c09144800000000 0x006048a240000000 0x000f9e7c0000000c 0x10007cf3e0000000

def z1644 : W := mkw 0x0c09144810012000 0x006048a240800900 0x5c0e1870f001c000 0x82e070c387800e00

def z1645 : W := mkw 0x7fdd5fef00000000 0x13feeaff78000000 0x7f8e19f300000000 0x83fc70cf98000000

def z1646 : W := mkw 0x7fcd5d6a69100000 0x1bfe6aeb53488000 0x7f8e187070000000 0x83fc70c383800000

def z1647 : W := mkw 0xb6d21f90fb71ff1e 0x05b690fc87db8ff8 0xfff19f8cfff9ff9f 0xffff8cfc67ffcffc

def z1648 : W := mkw 0x4829a04d00000000 0x12414d0268000000 0x000f807c00000004 0x10007c03e0000000

def z1649 : W := mkw 0x5b6fe048edbe0102 0x0adb7f02476df008 0x7fffe00cfffe0197 0xebffff0067fff00c

def z1650 : W := mkw 0x49bdebef00000000 0x124def5f78000000 0x23ffffff0000000f 0xd11ffffff8000000

def z1651 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38fffff8e27ce7f 0xdd1c7ffffc713e73

def z1652 : W := mkw 0x7fcd5d6f00000000 0x13fe6aeb78000000 0x7f8e187f00000000 0x93fc70c3f8000000

def z1653 : W := mkw 0x5364e0004d8e0000 0x0a9b2700026c7000 0x7ff1e000fffe0017 0xebff8f0007fff000

def z1654 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f987c00000004 0x92e07cc3e0000000

def z1655 : W := mkw 0x00020010b0fb77b6 0x800010008587dbbd 0x80000000f1f9f390 0x24000000078fcf9c

def z1656 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0x7fffffff01fe319f 0xfbfffffff80ff18c

def z1657 : W := mkw 0x5b6fe005edbe00a0 0x8adb7f002f6df005 0xffffe18ffffe0fff 0xffffff0c7ffff07f

def z1658 : W := mkw 0x12420010c9204204 0x0092100086490210 0xfffe1870ffe1c21f 0xfffff0c387ff0e10

def z1659 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x800fe67f0038339d 0x74007f33f801c19c

def z1660 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e79f300060c6e 0xd91c73cf98003063

def z1661 : W := mkw 0x0030a28500000000 0x0001851428000000 0x007fffff0000000f 0xd003fffff8000000

def z1662 : W := mkw 0x7fedfd6f00000000 0x13ff6feb78000000 0x7ffff87f00000007 0xd3ffffc3f8000000

def z1663 : W := mkw 0x7ffdffef02ca9cb0 0x93ffefff781654e5 0xffffffff8fffffff 0xfffffffffc7fffff

def z1664 : W := mkw 0x01864932a634ca45 0x000c32499531a652 0xa38e79f3fe3fce7e 0xfd1c73cf9ff1fe73

def z1665 : W := mkw 0x3ec91d4800000000 0x01f648ea40000000 0x7f8e187000000000 0x83fc70c380000000

def z1666 : W := mkw 0x00020010a0304306 0x0000100085018218 0x8001860c0038339d 0x74000c306001c19c

def z1667 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0xfffe7ff3ffc1fc1b 0xeffff3ff9ffe0fe0

def z1668 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8f987000000005 0xc3fc7cc380000000

def z1669 : W := mkw 0x7ffdffef209a0000 0x1bffefff7904d000 0x7fffffff0018000f 0xd3fffffff800c000

def z1670 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0f9e7cf039f195 0xe2e07cf3e781cf8c

def z1671 : W := mkw 0x5b6fe005edbe00a0 0x8adb7f002f6df005 0x7fffe003fffe0077 0xebffff001ffff003

def z1672 : W := mkw 0x008209108624ca45 0x0004104884312652 0xa38018008e27ce70 0x8d1c00c004713e73

def z1673 : W := mkw 0x7fcd5d6a10012000 0x13fe6aeb50800900 0x7f8e1870f001c000 0x83fc70c387800e00

def z1674 : W := mkw 0x80020010ff75ff5f 0x0400100087fbaffa 0x80000000fffffff0 0x2c00000007ffffff

def z1675 : W := mkw 0xfffdffef5bcbbcb8 0x97ffefff7ade5de5 0xffffffffffd9fd9f 0xfffffffffffecfec

def z1676 : W := mkw 0xa4901fea1241bc18 0x152480ff50920de0 0x80001ff00001fc08 0x040000ff80000fe0

def z1677 : W := mkw 0xa4901fa71241bc18 0x152480fd38920de0 0x80001f830001fc08 0x040000fc18000fe0

def z1678 : W := mkw 0xb6521690df65fe5d 0x05b290b486fb2ff2 0xdc700600ffe7fe71 0x2ee3803007ff3ff3

def z1679 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0x7fff9e7cffc1f001 0xa3fffcf3e7fe0f80

def z1680 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x000fe07f00380384 0x10007f03f801c01c

def z1681 : W := mkw 0x492fe058a4be4306 0x0a497f02c525f218 0x000fe070003e0004 0x00007f038001f000

def z1682 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff00000e6f 0xd7fffffff8000073

def z1683 : W := mkw 0x0184492200000000 0x000c224910000000 0xa38e79f30020021e 0xd51c73cf98010010

def z1684 : W := mkw 0x5366e010fdbf6306 0x0a9b370087edfb18 0xa3f06000fffff392 0x2d1f830007ffff9c

def z1685 : W := mkw 0xa4901fb21241fe5d 0x052480fd90920ff2 0x80001ff00001fc08 0x040000ff80000fe0

def z1686 : W := mkw 0x0c09144830112102 0x006048a241808908 0x5c0e187070000000 0x82e070c383800000

def z1687 : W := mkw 0x080b0058b0316306 0x00405802c5818b18 0x8001800cf039f390 0x24000c006781cf9c

def z1688 : W := mkw 0x00020010a634ca45 0x000010008531a652 0x80000000fe3fce70 0x2c00000007f1fe73

def z1689 : W := mkw 0x0400140000000000 0x002000a000000000 0x5c0e1e700000000d 0xd2e070f380000000

def z1690 : W := mkw 0x0c1916c800000000 0x0060c8b640000000 0x5c7f9ffc0000000f 0xd2e3fcffe0000000

def z1691 : W := mkw 0x00020010efbeca45 0x08001000877df652 0x00000000ffffc010 0x2800000007fffe00

def z1692 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e79f38e27ce72 0x8d1c73cf9c713e73

def z1693 : W := mkw 0x492de06f00000000 0x12496f0378000000 0x238fe07f00000006 0xd11c7f03f8000000

def z1694 : W := mkw 0x008209108220ca04 0x0004104884110650 0xa38019808e21ce1a 0xcd1c00cc04710e70

def z1695 : W := mkw 0x5b6fe032edbe4245 0x0adb7f01976df212 0xffffe1f3fffe0e7f 0xffffff0f9ffff073

def z1696 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e1e7000000009 0xc3fc70f380000000

def z1697 : W := mkw 0x7ffdffef06048841 0x13ffefff78302442 0x7fffffff0e00000f 0xd3fffffff8700000

def z1698 : W := mkw 0x0d8d5d6a00000000 0x006c6aeb50000000 0xff8fffff003e3fff 0xfffc7ffff801f1ff

def z1699 : W := mkw 0x0000000000000000 0x0000000000000000 0x800e18700020021c 0xd40070c380010010

def z1700 : W := mkw 0x7ffdffef00401410 0x13ffefff780200a0 0xffffffff01e63e7f 0xfffffffff80f31f3

def z1701 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f9e7c0038001d 0xf2e07cf3e001c000

def z1702 : W := mkw 0xb7d45fa25b41bc18 0x05bea2fd12da0de0 0xfffe1ff0ffc1fc1b 0xeffff0ff87fe0fe0

def z1703 : W := mkw 0x01944ba7004014b0 0x800ca25d380200a5 0xa38e7fff00003fee 0xd51c73fff80001ff

def z1704 : W := mkw 0x04821d10b635eb47 0x002410e885b1af5a 0xff801f80fe3ffffb 0xeffc00fc07f1ffff

def z1705 : W := mkw 0xb6d01f855b41bcb8 0x85b680fc2ada0de5 0xfff01f8cffc1fd9b 0xefff80fc67fe0fec

def z1706 : W := mkw 0x7ffdffef30db35b2 0x93ffefff7986d9ad 0x7fffffff71d8318f 0xf3fffffffb8ec18c

def z1707 : W := mkw 0x7ffdffef20100000 0x13ffefff79008000 0x7fffffff7018000f 0xf3fffffffb80c000

def z1708 : W := mkw 0xb6d21f90db61fe1c 0x05b690fc86db0ff0 0xfff01f80ffe1fe1b 0xefff80fc07ff0ff0

def z1709 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80006183f03ffffe 0x7c00030c1f81ffff

def z1710 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff00000c1f 0xdffffffff8000060

def z1711 : W := mkw 0x49ade96f00000000 0x124d6f4b78000000 0x238ff87f00000004 0x911c7fc3f8000000

def z1712 : W := mkw 0x0106401084244204 0x0008320084212210 0xa38e79f38e27ce7e 0xdd1c73cf9c713e73

def z1713 : W := mkw 0x7ffdffef008a0000 0x13ffefff78045000 0x7fffffff003e000f 0xd3fffffff801f000

def z1714 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01f83ffc1fe7b 0xffff80fc1ffe0ff3

def z1715 : W := mkw 0x7bfdebef00000000 0x13dfef5f78000000 0x23ffe7ff0000000f 0x511fff3ff8000000

def z1716 : W := mkw 0x5b4f4000ed340000 0x0ada7a000769a000 0x7ffe0000ffc00001 0xa3fff00007fe0000

def z1717 : W := mkw 0x49ade96f008a00a0 0x924d6f4b78045005 0xa38ff9ff003e0ffe 0xdd1c7fcff801f07f

def z1718 : W := mkw 0x7fcd5d6a06048841 0x13fe6aeb50302442 0x7f8e79f30e060c62 0x8bfc73cf98703063

def z1719 : W := mkw 0x5a69a000699a0000 0x0ad34d00034cd000 0x7ff1e000fffe0017 0xebff8f0007fff000

def z1720 : W := mkw 0x7ffdffef004014b0 0x93ffefff780200a5 0x7fffffff00000c6f 0xd3fffffff8000063

def z1721 : W := mkw 0x0020a000008a0000 0x0001050000045000 0x8071e78f01fe3fff 0x7c038f3c780ff1ff

def z1722 : W := mkw 0xa4901fa21241bc59 0x052480fd10920de2 0x80001f830001fc68 0x040000fc18000fe3

def z1723 : W := mkw 0x5bfdeba700ca14b0 0x82dfef5d380650a5 0xffffffff01fe3fff 0xfffffffff80ff1ff

def z1724 : W := mkw 0x00020010ef34ca45 0x080010008779a652 0x80000000fe27ce70 0x0c00000007f13e73

def z1725 : W := mkw 0x6dbdffef00ca14b0 0x936defff780650a5 0x807fffff01fe3fff 0x7c03fffff80ff1ff

def z1726 : W := mkw 0x7ffdffef04040041 0x13ffefff78202002 0x7fffffff0006006f 0xd3fffffff8003003

def z1727 : W := mkw 0x080b0010a0304204 0x0040580085018210 0xdc0f9e7cf039f39d 0xf6e07cf3e781cf9c

def z1728 : W := mkw 0x7ffdffef008a00a0 0x93ffefff78045005 0x7fffffff01fe03ff 0xfbfffffff80ff01f

def z1729 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38061838e27ce7e 0x5d1c030c1c713e73

def z1730 : W := mkw 0x01a4e927008a00a0 0x800d274938045005 0x238ff9ff003e03ee 0xd11c7fcff801f01f

def z1731 : W := mkw 0x1b4f4000ed340000 0x00da7a000769a000 0x7fffe000fffe0017 0xebffff0007fff000

def z1732 : W := mkw 0xfffdffef5b01a808 0x17ffefff7ad80d40 0xfffffffffe01f01f 0xf7fffffffff00f80

def z1733 : W := mkw 0x0030a28500ca14b0 0x80018514280650a5 0x8071ff8f81ffffff 0xfc038ffc7c0fffff

def z1734 : W := mkw 0x0032a295effedef5 0x88019514af7ff6f7 0x8071e78fffffffff 0x7c038f3c7fffffff

def z1735 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff01f80ffe1fe1f 0xffff80fc07ff0ff0

def z1736 : W := mkw 0x53e4e92200000000 0x029f274910000000 0x23fe79f30000000e 0xd11ff3cf98000000

def z1737 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800060038e27ce74 0x1c0003001c713e73

def z1738 : W := mkw 0x7fdd5fef004014b0 0x93feeaff780200a5 0xff8e1fff00003fe8 0x97fc70fff80001ff

def z1739 : W := mkw 0x00020010effedef5 0x88001000877ff6f7 0x80000000fffffff0 0x2c00000007ffffff

def z1740 : W := mkw 0xffdd5fea59413418 0x17feeaff52ca09a0 0x7ffe1e7071c03001 0xa3fff0f3838e0180

def z1741 : W := mkw 0xf7f4ffa75b41bc18 0x17bfa7fd3ada0de0 0xfffe7ff3ffc1fc1f 0xfffff3ff9ffe0fe0

def z1742 : W := mkw 0x53e4e9224d8e0000 0x0a9f2749126c7000 0x23fe79f30fc6000e 0xd91ff3cf987e3000

def z1743 : W := mkw 0x7ffdffef008a00a0 0x93ffefff78045005 0x7fffffff0006006f 0xd3fffffff8003003

def z1744 : W := mkw 0x4d2df46f008a00a0 0x92696fa378045005 0xdc0ffe7f003e33fd 0xf6e07ff3f801f19f

def z1745 : W := mkw 0x73c4492200000000 0x139e224910000000 0x238e187000000000 0x811c70c380000000

def z1746 : W := mkw 0x0000000000000000 0x0000000000000000 0x800e18708001c01c 0xd40070c384000e00

def z1747 : W := mkw 0x0184492200000000 0x000c224910000000 0x238e19f00000000a 0xc11c70cf80000000

def z1748 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238e79f38e27cc76 0xc91c73cf9c713e63

def z1749 : W := mkw 0x0032a295fdff77b6 0x88019514afeffbbd 0x8071e78fffffffff 0x7c038f3c7fffffff

def z1750 : W := mkw 0x0184492200ca14b0 0x800c2249100650a5 0xa38e79f301fe3ffe 0xfd1c73cf980ff1ff

def z1751 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9ffff039fffd 0xf6e07cffff81cfff

def z1752 : W := mkw 0x7ffdffef10012102 0x13ffefff78800908 0x7fffffff0000318f 0xd3fffffff800018c

def z1753 : W := mkw 0x2c1916cd00000000 0x1160c8b668000000 0x5c0f9e7c0000000d 0xd2e07cf3e0000000

def z1754 : W := mkw 0x5b6de0006d9e0000 0x0adb6f00036cf000 0x7ff180007fd80001 0x23ff8c0003fec000

def z1755 : W := mkw 0x008209108624ca45 0x0004104884312652 0xa38001808e27ce72 0x0d1c000c04713e73

def z1756 : W := mkw 0x492fe05da4be43a6 0x8a497f02ed25f21d 0x000fe07f003e03e4 0x10007f03f801f01f

def z1757 : W := mkw 0x5b6de06f00000000 0x12db6f0378000000 0x5c7fe07f00000005 0x12e3ff03f8000000

def z1758 : W := mkw 0x73f4eba700ca14b0 0x939fa75d380650a5 0xa3fe79f301e60e7e 0xdd1ff3cf980f3073

def z1759 : W := mkw 0xb6d21f90df65fe5d 0x05b690fc86fb2ff2 0xfff07f83ffe7fe7f 0xffff83fc1fff3ff3

def z1760 : W := mkw 0x00020010b0717716 0x0000100085838bb8 0x80000000f1f9ff90 0x2c000000078fcffc

def z1761 : W := mkw 0x000200108220ca04 0x0000100084110650 0x800000008e21ce10 0x0c00000004710e70

def z1762 : W := mkw 0xb7d45fa24f449c59 0x05bea2fd127a24e2 0x7ffe7ff30fc60c6f 0xdbfff3ff987e3063

def z1763 : W := mkw 0xa4901f801241bc18 0x052480fc00920de0 0x80019f8c0039ff9d 0x74000cfc6001cffc

def z1764 : W := mkw 0x80020010df25ea4d 0x0400100086f92f52 0x00000000fe01c000 0x0000000007f00e00

def z1765 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff0000338f 0xd7fffffff800019c

def z1766 : W := mkw 0x5b6fe07aedbe4347 0x0adb7f03d76df21a 0x7fffe07ffffe03f7 0xfbffff03fffff01f

def z1767 : W := mkw 0x7fdd5fea00000000 0x13feeaff50000000 0x7ffe19f000000002 0x83fff0cf80000000

def z1768 : W := mkw 0x498d496a00000000 0x124c6a4b50000000 0x238e187000000000 0x811c70c380000000

def z1769 : W := mkw 0xa4901fc81241bd1a 0x052480fe40920de8 0x80001f8c0001fd88 0x040000fc60000fec

def z1770 : W := mkw 0x0022a015b0bb63a6 0x80011500ad85db1d 0x8001e00ff03ff3f4 0x34000f007f81ff9f

def z1771 : W := mkw 0x0839a2cd00000000 0x0041cd1668000000 0x007fe7ff0000000f 0x5003ff3ff8000000

def z1772 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffff9ff00000006 0x93ffffcff8000000

def z1773 : W := mkw 0xb6c21d10fb31eb0e 0x05b610e887d98f58 0xff801800fe39f390 0xa7fc00c007f1cf9c

def z1774 : W := mkw 0x0d0d544800000000 0x00686aa240000000 0x7f8ffe7c0000000f 0xd3fc7ff3e0000000

def z1775 : W := mkw 0xb6f2bf95fbfbffbe 0x85b795fcafdfdffd 0xfff1ff8fffffffff 0xffff8ffc7fffffff

def z1776 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffff9f300000007 0xc3ffffcf98000000

def z1777 : W := mkw 0x80120290fb71ff1e 0x0400901487db8ff8 0x8071878cfff9ff9f 0x7c038c3c67ffcffc

def z1778 : W := mkw 0x0104402204040041 0x0008220110202002 0x000e607300060064 0x1000730398003003

def z1779 : W := mkw 0xb6d01f805b41bcb8 0x85b680fc02da0de5 0xfff01f80ffc1fffb 0xefff80fc07fe0fff

def z1780 : W := mkw 0x92c009005b41bc18 0x0496004802da0de0 0xfff01980ffc1fc1b 0xefff80cc07fe0fe0

def z1781 : W := mkw 0x0d8d5d6a00000000 0x006c6aeb50000000 0x7f8e187000000000 0x83fc70c380000000

def z1782 : W := mkw 0x6d3df6ef00000000 0x1369efb778000000 0x000fe67f00000004 0x10007f33f8000000

def z1783 : W := mkw 0xf3f4eba74b409c18 0x179fa75d3a5a04e0 0xa3fe79f38fc1cc1e 0xdd1ff3cf9c7e0e60

def z1784 : W := mkw 0xa4921f909261fe1c 0x052490fc84930ff0 0x800e1ff08021fe1c 0xd40070ff84010ff0

def z1785 : W := mkw 0x0c09144820100102 0x006048a241008008 0x5c0f9e7c0018018d 0xd2e07cf3e000c00c

def z1786 : W := mkw 0x7ffdffef06ce9cf1 0x93ffefff783674e7 0xffffffff0ffe3fff 0xfffffffff87ff1ff

def z1787 : W := mkw 0x0002001080204204 0x0000100084010210 0x800000008027ce70 0x0c00000004013e73

def z1788 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0xffffffff71c1fc0f 0xf7fffffffb8e0fe0

def z1789 : W := mkw 0x5b6fe010edbe4204 0x0adb7f00876df210 0xfffffe7cfffff39f 0xfffffff3e7ffff9c

def z1790 : W := mkw 0x493de2ef004014b0 0x9249ef17780200a5 0x800fe7ff00003fec 0x14007f3ff80001ff

def z1791 : W := mkw 0xac991fef1241bc18 0x1564c8ff78920de0 0xdc0f9ffff001fc1d 0xf6e07cffff800fe0

def z1792 : W := mkw 0x0c09144800000000 0x006048a240000000 0xdc0f9e7c0000338d 0xd6e07cf3e000019c

def z1793 : W := mkw 0x7fcd5d6a02008800 0x13fe6aeb50100440 0x7f8e18708e01c000 0x83fc70c384700e00

def z1794 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0x5c0f9e7cf019f18d 0xf2e07cf3e780cf8c

def z1795 : W := mkw 0x0c09144800000000 0x006048a240000000 0x5c0f987000000005 0xc2e07cc380000000

def z1796 : W := mkw 0x53e6e932efbeca45 0x0a9f3749977df652 0xa3f06183ffffce72 0x2d1f830c1ffffe73

def z1797 : W := mkw 0xbed91fc84b409c18 0x05f6c8fe425a04e0 0x7fff9ffc0fc00c0f 0xdbfffcffe07e0060

def z1798 : W := mkw 0x0002001080204204 0x0000100084010210 0x800000008039f390 0x240000000401cf9c

def z1799 : W := mkw 0x008209108624ca45 0x0004104884312652 0xa38079838e27ce7e 0xdd1c03cc1c713e73

def z1800 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7ffe7fff0000000a 0x93fff3fff8000000

def z1801 : W := mkw 0x80020010f971771e 0x0400100087cb8bb8 0x80000000f1f9f390 0x24000000078fcf9c

def z1802 : W := mkw 0x7ffdffef004014b0 0x93ffefff780200a5 0x7fffffff0000318f 0xd3fffffff800018c

def z1803 : W := mkw 0x0c3bb6ddb0fb77b6 0x8061ddb6ed87dbbd 0xdc71860cf1fffff1 0x2ee38c30678fffff

def z1804 : W := mkw 0x7ffdffef10413410 0x13ffefff788209a0 0xfffffffff1c1fc1f 0xffffffffff8e0fe0

def z1805 : W := mkw 0x00820910b231eb06 0x0004104885918f58 0xa3801980fe39ff9a 0xed1c00cc07f1cffc

def z1806 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff0000301f 0xf7fffffff8000180

def z1807 : W := mkw 0x7ffdffea00000000 0x13ffefff50000000 0x7ffffff00000000f 0xc3ffffff80000000

def z1808 : W := mkw 0xbed91fc87951351a 0x05f6c8fe43ca89a8 0x7fff9ffc71d8318f 0xf3fffcffe38ec18c

def z1809 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f9e7c0000000d 0xd0007cf3e0000000

def z1810 : W := mkw 0x00120290b0717716 0x0000901485838bb8 0x80700780f1f9ff9b 0x6c03803c078fcffc

def z1811 : W := mkw 0x01b4eba706ce9cf1 0x800da75d383674e7 0x23ffffff0fc60c6f 0xd91ffffff87e3063

def z1812 : W := mkw 0x7e79b6cd00000000 0x13f3cdb668000000 0x5c7fffff0000000f 0xd2e3fffff8000000

def z1813 : W := mkw 0x0184492200000000 0x000c224910000000 0xa38e79f300000c1e 0xdd1c73cf98000060

def z1814 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xffffe000fffe021f 0xffffff0007fff010

def z1815 : W := mkw 0x12d00b804b409c10 0x0096805c025a04e0 0xfff01f80ffc1fc1b 0xefff80fc07fe0fe0

def z1816 : W := mkw 0xb6d21f90fbfbffbe 0x85b690fc87dfdffd 0xfff01f80fffffffb 0xefff80fc07ffffff

def z1817 : W := mkw 0x00020010a0304204 0x0000100085018210 0x80000000f039c210 0x240000000781ce10

def z1818 : W := mkw 0x2cb9bfef00000000 0x1165cdff78000000 0x5c7fffff0000000f 0xd2e3fffff8000000

def z1819 : W := mkw 0x0d8d5d6a06048841 0x006c6aeb50302442 0x7f8fffff0e060c6f 0xdbfc7ffff8703063

def z1820 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e79f38e27ce6c 0x951c73cf9c713e73

def z1821 : W := mkw 0x000200108624ca45 0x0000100084312652 0x800000008e21c210 0x0400000004710e10

def z1822 : W := mkw 0x4c29b44d00000000 0x12614da268000000 0x5c0f9e7c0000000d 0xd2e07cf3e0000000

def z1823 : W := mkw 0xb6c01d005b41bc18 0x05b600e802da0de0 0xfff01800ffc1fc13 0xefff80c007fe0fe0

def z1824 : W := mkw 0x7f6df46f00000000 0x13fb6fa378000000 0x5c0fe07f00000004 0x12e07f03f8000000

def z1825 : W := mkw 0x04021410b0316306 0x002010a085818b18 0x5c001800f001c000 0x82e000c007800e00

def z1826 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0xffffffff003e3fff 0xfffffffff801f1ff

def z1827 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e79f300000002 0x83fc73cf98000000

def z1828 : W := mkw 0xb2d20b90cf64de5d 0x0596905c867b26f2 0xa3f001808fe7ce72 0x0d1f800c047f3e73

def z1829 : W := mkw 0x77f4ffef00000000 0x13bfa7ff78000000 0x23fe7fff0000000e 0xd11ff3fff8000000

def z1830 : W := mkw 0x36d21f908624ca45 0x01b690fc84312652 0xfff01f808e27ce7b 0xcfff80fc04713e73

def z1831 : W := mkw 0x7f7df6ef00000000 0x13fbefb778000000 0x5c7f867c00000001 0x02e3fc33e0000000

def z1832 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8e787000000006 0xc3fc73c380000000

def z1833 : W := mkw 0x0c0b1458b0316306 0x006058a2c5818b18 0xdc0f9ffcf039ff9f 0xfee07cffe781cffc

def z1834 : W := mkw 0x73f4eba700000000 0x139fa75d38000000 0x23fe79f300000002 0x811ff3cf98000000

def z1835 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff19f80fff9fc1f 0xefff8cfc07ffcfe0

def z1836 : W := mkw 0x0184492204040041 0x000c224910202002 0x238e79f30006006e 0xd11c73cf98003003

def z1837 : W := mkw 0x018649328624ca45 0x000c324994312652 0xa38e79f38e07cc7a 0xcd1c73cf9c703e63

def z1838 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff07f83ffc7fc7b 0xefff83fc1ffe3fe3

def z1839 : W := mkw 0x5366e010cfaeca45 0x0a9b3700867d7652 0xa3f060008fe7ce72 0x0d1f8300047f3e73

def z1840 : W := mkw 0x01b4eba702ca9cb0 0x800da75d381654e5 0xa3ffffff8fffffff 0xfd1ffffffc7fffff

def z1841 : W := mkw 0x7ffdffef00000000 0x13ffefff78000000 0x7fffffff0038038f 0xd3fffffff801c01c

def z1842 : W := mkw 0x1366e000cdae0000 0x009b3700066d7000 0x7fffe000fffe0017 0xebffff0007fff000

def z1843 : W := mkw 0x490d406a00000000 0x12486a0350000000 0x000f807c00000004 0x10007c03e0000000

def z1844 : W := mkw 0x0104400000000000 0x0008220000000000 0x238e78700000000e 0xd11c73c380000000

def z1845 : W := mkw 0x0002001084244245 0x0000100084212212 0x800000008027c270 0x0400000004013e13

def z1846 : W := mkw 0xb6c01d005b01a808 0x05b600e802d80d40 0xfff01e00ffc1f01b 0xefff80f007fe0f80

def z1847 : W := mkw 0xffdd5fea5b41bc18 0x17feeaff52da0de0 0xffff9ffcffc1fc1f 0xfffffcffe7fe0fe0

def z1848 : W := mkw 0x01a4e922008a0000 0x000d274910045000 0x23fff9f301fe001f 0xf91fffcf980ff000

def z1849 : W := mkw 0x00020010b4356306 0x0000100085a1ab18 0x80000000fe3ff390 0x2c00000007f1ff9c

def z1850 : W := mkw 0xb6d01f805b41bc18 0x05b680fc02da0de0 0xfff07f80ffe7fc1f 0xefff83fc07ff3fe0

def z1851 : W := mkw 0x5f7df6cd00000000 0x02fbefb668000000 0x7fffffff0000000f 0xd3fffffff8000000

def z1852 : W := mkw 0x36d01f8059012000 0x01b680fc02c80900 0xfff01f80ffc1f01b 0xefff80fc07fe0f80

def z1853 : W := mkw 0x4124e02700000000 0x1209270138000000 0x000e607300000004 0x1000730398000000

def z1854 : W := mkw 0xfffdffef5b41bc18 0x17ffefff7ada0de0 0xffffffff0fc1fc0f 0xdffffffff87e0fe0

def z1855 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xffffe600fffe301f 0xefffff3007fff180

def z1856 : W := mkw 0x7fdd5fef00000000 0x13feeaff78000000 0x7f8e1e7c00000000 0x83fc70f3e0000000

def z1857 : W := mkw 0x0c39b6cd10413410 0x0061cdb6688209a0 0xdc7ffffff1c1fc1f 0xfee3ffffff8e0fe0

def z1858 : W := mkw 0x0184492206048841 0x000c224910302442 0xa38e79f30e260e7e 0xdd1c73cf98713073

def z1859 : W := mkw 0x4d2df46f30112102 0x12696fa379808908 0x5c0fe67f70183185 0x32e07f33fb80c18c

def z1860 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0xffffe78ffffe3fff 0xffffff3c7ffff1ff

def z1861 : W := mkw 0x0d8d5d6a1201a800 0x006c6aeb50900d40 0xff8ffffffe01fc1f 0xfffc7ffffff00fe0

def z1862 : W := mkw 0x80020010fffffe5d 0x0c00100087fffff2 0x80000000fffffe70 0x2c00000007fffff3

def z1863 : W := mkw 0x00020010ffbfeb47 0x0800100087fdff5a 0x80000000fffffff0 0x2c00000007ffffff

def z1864 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0xff8e79f300260e7e 0xdffc73cf98013073

def z1865 : W := mkw 0x010640108624ca45 0x0008320084312652 0xa38060008e27ce72 0x0d1c030004713e73

def z1866 : W := mkw 0x7ffdffef4d040000 0x1bffefff7a682000 0x7fffffff0e00000f 0xd3fffffff8700000

def z1867 : W := mkw 0x37d45fa200401410 0x01bea2fd100200a0 0xfffe7ff301e63e7f 0xfffff3ff980f31f3

def z1868 : W := mkw 0x000200108624ca45 0x0000100084312652 0x000000008e27c010 0x0800000004713e00

def z1869 : W := mkw 0x00020010fd356306 0x0800100087e9ab18 0x00000000fe01c000 0x0000000007f00e00

def z1870 : W := mkw 0x964014005b41bc18 0x04b200a002da0de0 0xfff01e00ffc1fc1b 0xefff80f007fe0fe0

def z1871 : W := mkw 0x018649328624ca45 0x000c324994312652 0x238061838e07cc62 0x091c030c1c703e63

def z1872 : W := mkw 0x7ffdffef000000a0 0x93ffefff78000005 0x7fffffff000003ef 0xd3fffffff800001f

def z1873 : W := mkw 0x098d496a00000000 0x004c6a4b50000000 0x238ff9ff0000000e 0xd11c7fcff8000000

def z1874 : W := mkw 0x7fcd5d6a00000000 0x13fe6aeb50000000 0x7f8f9e7c00000001 0x83fc7cf3e0000000

def z1875 : W := mkw 0x0829a04d008a00a0 0x80414d0268045005 0x000fe07f003e03e4 0x10007f03f801f01f

def z1876 : W := mkw 0x0402141090216204 0x002010a084810b10 0xdc001e00f021f219 0xe6e000f007810f90

def z1877 : W := mkw 0x5b6fe000edbe0000 0x0adb7f00076df000 0x7fffe000fffe0006 0x8bffff0007fff000

def z1878 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80018000f039f395 0x64000c000781cf9c

def z1879 : W := mkw 0x04021458b0316306 0x002010a2c5818b18 0x8000060cf039f390 0x240000306781cf9c

def z1880 : W := mkw 0x7ffdffa200000000 0x03ffeffd10000000 0x7ffffff30000000f 0xd3ffffff98000000

def z1881 : W := mkw 0x00b2ab9586eedef5 0x8005955cac3776f7 0xa3f1ff8f8fffffff 0xfd1f8ffc7c7fffff

def z1882 : W := mkw 0x7ffdffef00401410 0x13ffefff780200a0 0x7fffffff01c0300f 0xf3fffffff80e0180

def z1883 : W := mkw 0x7fdd5fef00000000 0x13feeaff78000000 0x7ffe1fff0000000b 0xd3fff0fff8000000

def z1884 : W := mkw 0x7b7de2ef00000000 0x13dbef1778000000 0x007fe07f00000004 0x1003ff03f8000000

def z1885 : W := mkw 0x7ffdffef699a0000 0x1bffefff7b4cd000 0x7fffffff71fe001f 0xfbfffffffb8ff000

def z1886 : W := mkw 0x00020010b0316306 0x0000100085818b18 0x80000000f039f39c 0x740000000781cf9c

def z1887 : W := mkw 0x0000000000000000 0x0000000000000000 0x000e79f30000000e 0xd00073cf98000000

def z1888 : W := mkw 0x00020010a0304306 0x0000100085018218 0x0000000000000000 0x0000000000000000

def z1889 : W := mkw 0x7bfdebef00ca14b0 0x93dfef5f780650a5 0x23ffe1ff01fe0fe6 0x191fff0ff80ff07f

def z1890 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0xffffffff01e60e7f 0xdffffffff80f3073

def z1891 : W := mkw 0x00020010b635eb47 0x0000100085b1af5a 0x00000000fe01c000 0x0000000007f00e00

def z1892 : W := mkw 0x0104402200000000 0x0008220110000000 0x000e607300260264 0x1000730398013013

def z1893 : W := mkw 0x7fcd5d6a06048841 0x13fe6aeb50302442 0x7f8e18700e000000 0x83fc70c380700000

def z1894 : W := mkw 0x7ffdffef00ca14b0 0x93ffefff780650a5 0xffffffff01f8339f 0xf7fffffff80fc19c

def z1895 : W := mkw 0x5a49000069100000 0x0ad2480003488000 0x7ff00000ffc00013 0xebff800007fe0000

def z1896 : W := mkw 0x16c01d005b01a800 0x00b600e802d80d40 0xfff01f80ffc1fc1b 0xefff80fc07fe0fe0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z5,z8,z6]),(0,[z9,z1,z2,z3,z5,z8,z10]),(0,[z1,z11,z2,z3,z5,z12,z6])],[(0,[z1,z2,z3,z13,z5,z8,z6]),(0,[z1,z2,z3,z14,z5,z8,z6])],[(1,[z1,z2,z3,z5,z8,z6]),(0,[z15,z1,z16,z3,z5,z8,z6]),(0,[z17,z1,z2,z3,z5,z18,z6])],[(0,[z15,z1,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z19,z20,z6])],[(1,[z1,z2,z3,z21,z20,z6]),(0,[z1,z2,z22,z3,z5,z8,z6]),(0,[z23,z1,z2,z3,z5,z8,z6])],[(0,[z24,z1,z2,z3,z5,z8,z6]),(0,[z17,z1,z25,z2,z3,z5,z6]),(0,[z1,z2,z26,z3,z5,z6,z27])],[(0,[z28,z1,z2,z3,z5,z29,z6]),(0,[z1,z2,z3,z5,z30,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z31]),(0,[z1,z2,z32,z3,z5,z8,z6])],[(0,[z1,z2,z3,z33,z5,z34,z6])],[(1,[z1,z2,z35,z5,z8,z6]),(0,[z36,z1,z2,z3,z5,z8,z37]),(0,[z1,z2,z3,z38,z5,z6,z27])],[(0,[z39,z1,z2,z3,z5,z8,z6]),(0,[z17,z15,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z40,z41,z6]),(0,[z1,z2,z3,z42,z8,z10,z6]),(0,[z43,z1,z2,z3,z33,z5,z6]),(0,[z1,z44,z2,z3,z5,z45,z6]),(0,[z1,z2,z3,z5,z8,z6,z46]),(0,[z1,z2,z47,z48,z3,z5,z6])],[],[(0,[z2,z49,z3,z4,z5,z8,z6]),(1,[z2,z3,z5,z41,z21,z6]),(0,[z1,z2,z3,z5,z50,z8,z6]),(0,[z1,z2,z51,z3,z5,z8,z6]),(0,[z1,z2,z52,z3,z5,z8,z6])],[(0,[z28,z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z53,z5,z41,z6])],[(0,[z1,z2,z3,z41,z8,z20,z6])],[(0,[z54,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z55]),(0,[z1,z56,z2,z57,z3,z5,z6]),(0,[z58,z1,z2,z3,z59,z8,z6])]],
   [[(0,[z7,z1,z2,z49,z3,z5,z6]),(0,[z17,z1,z2,z3,z5,z10,z6]),(1,[z43,z1,z60,z5,z8,z6]),(0,[z1,z2,z61,z3,z5,z8,z6]),(0,[z62,z1,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z63,z8,z20,z6]),(0,[z1,z2,z64,z3,z5,z8,z6])],[(1,[z1,z2,z3,z65,z8,z6]),(1,[z1,z66,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z67,z6]),(0,[z1,z2,z3,z53,z5,z8,z68])],[(0,[z1,z2,z57,z3,z3,z5,z6]),(0,[z1,z2,z57,z3,z5,z6,z69])],[(0,[z1,z2,z3,z5,z21,z6,z70]),(0,[z1,z2,z71,z3,z42,z8,z6]),(0,[z1,z2,z5,z8,z72,z6,z69])],[(0,[z1,z2,z3,z5,z73,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z74]),(0,[z1,z2,z3,z75,z5,z8,z6]),(0,[z1,z2,z3,z5,z76,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z77])],[(0,[z1,z2,z3,z5,z8,z78,z6])],[(1,[z1,z2,z3,z79,z5,z6]),(1,[z1,z2,z3,z5,z8,z80]),(0,[z1,z2,z3,z5,z81,z8,z6]),(0,[z82,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z8,z34,z6]),(0,[z1,z2,z3,z5,z8,z83,z6])],[(0,[z1,z56,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z41,z6,z84]),(0,[z1,z2,z85,z3,z5,z8,z6]),(1,[z17,z1,z2,z3,z42,z6])],[(1,[z1,z86,z2,z3,z5,z6]),(0,[z1,z2,z57,z3,z87,z5,z6])],[(0,[z1,z2,z3,z5,z88,z41,z6]),(0,[z43,z1,z3,z60,z5,z8,z6]),(0,[z1,z11,z2,z51,z3,z5,z6]),(0,[z1,z2,z3,z89,z8,z20,z6]),(0,[z62,z1,z2,z3,z5,z8,z6]),(0,[z90,z1,z2,z3,z5,z8,z6])],[(0,[z36,z17,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z91,z8,z6])],[(0,[z1,z2,z3,z92,z8,z20,z6]),(0,[z1,z2,z3,z93,z5,z21,z6]),(0,[z1,z2,z48,z57,z3,z5,z6])],[(0,[z36,z1,z2,z3,z5,z94,z6]),(0,[z1,z2,z95,z3,z5,z8,z6]),(0,[z1,z2,z3,z33,z5,z92,z6]),(0,[z1,z2,z3,z5,z8,z6,z96]),(0,[z1,z44,z2,z3,z5,z8,z97]),(0,[z1,z2,z57,z3,z59,z5,z6])],[(1,[z7,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z5,z8,z6]),(0,[z1,z2,z3,z98,z5,z41,z6]),(0,[z1,z11,z2,z3,z60,z5,z6]),(0,[z99,z1,z2,z3,z5,z89,z6]),(0,[z1,z2,z100,z3,z101,z8,z6]),(0,[z1,z2,z3,z102,z5,z8,z6]),(0,[z1,z2,z3,z42,z5,z103,z6])],[(0,[z36,z1,z2,z3,z104,z8,z6]),(0,[z1,z105,z2,z3,z5,z8,z6])],[(0,[z43,z1,z2,z3,z5,z41,z6]),(0,[z1,z11,z2,z3,z106,z5,z6]),(0,[z1,z2,z47,z57,z3,z5,z6])]],
   [[(0,[z107,z1,z2,z57,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z6,z108])],[(0,[z109,z1,z2,z3,z5,z8,z6])],[(0,[z110,z1,z2,z3,z5,z21,z6]),(0,[z111,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z112,z8,z6])],[(0,[z1,z2,z48,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z113,z8,z6])],[(1,[z1,z2,z3,z114,z8,z6]),(0,[z1,z2,z3,z5,z8,z115,z6]),(1,[z116,z1,z2,z5,z88,z6])],[(0,[z117,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z57,z3,z93,z5,z6]),(0,[z1,z2,z3,z118,z5,z41,z6])],[(0,[z119,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z120,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z121]),(0,[z1,z2,z3,z5,z41,z122,z6]),(0,[z9,z1,z2,z3,z123,z8,z6]),(0,[z124,z1,z2,z3,z5,z8,z6]),(0,[z1,z11,z2,z3,z5,z97,z6]),(0,[z1,z2,z125,z3,z5,z8,z6])],[(0,[z1,z2,z100,z3,z5,z8,z6]),(0,[z1,z2,z3,z126,z5,z8,z6])],[(0,[z1,z2,z57,z3,z5,z6,z84]),(0,[z1,z2,z127,z3,z5,z8,z6]),(0,[z116,z1,z56,z2,z3,z5,z6]),(1,[z1,z2,z3,z128,z8,z6]),(0,[z1,z2,z3,z33,z5,z40,z6])],[(0,[z129,z1,z11,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z5,z130,z6]),(0,[z1,z2,z3,z33,z5,z6,z27])],[(0,[z15,z1,z2,z3,z8,z20,z6]),(0,[z116,z1,z2,z3,z5,z92,z6]),(0,[z9,z1,z2,z57,z3,z5,z6])],[(0,[z131,z2,z3,z93,z5,z8,z6]),(0,[z1,z2,z3,z5,z65,z8,z6])],[(0,[z1,z132,z2,z3,z5,z8,z6]),(0,[z15,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z5,z133,z8,z6]),(0,[z1,z2,z134,z3,z5,z8,z6]),(0,[z135,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z136,z5,z8,z6])],[(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z1,z11,z2,z3,z5,z89,z6]),(0,[z17,z1,z2,z3,z87,z5,z6]),(0,[z1,z2,z3,z87,z5,z6,z27])],[(0,[z137,z1,z2,z138,z5,z8,z6]),(0,[z1,z2,z139,z3,z5,z8,z6]),(0,[z140,z1,z2,z3,z5,z21,z6]),(0,[z1,z11,z2,z3,z5,z72,z6]),(0,[z1,z25,z2,z3,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z5,z141,z8,z6]),(0,[z1,z2,z3,z33,z5,z18,z6])],[(2,[z1,z2,z3,z42,z27])],[(0,[z142,z1,z2,z3,z5,z8,z6]),(0,[z43,z116,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z143,z5,z6]),(0,[z17,z1,z2,z3,z59,z5,z6]),(0,[z144,z1,z2,z3,z5,z8,z6])],[(0,[z145,z1,z2,z3,z5,z8,z6]),(0,[z1,z51,z3,z60,z5,z8,z6]),(0,[z1,z146,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z6,z27,z27])],[(0,[z1,z2,z3,z147,z5,z21,z6])],[(0,[z148,z1,z11,z2,z3,z5,z6]),(1,[z17,z1,z3,z5,z149,z6])],[(0,[z1,z150,z2,z3,z5,z8,z6]),(0,[z151,z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z5,z149,z6,z27]),(0,[z1,z2,z57,z3,z101,z5,z6])],[(0,[z1,z2,z152,z3,z5,z8,z6]),(0,[z153,z1,z2,z3,z5,z8,z6]),(0,[z154,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z155,z33,z5,z6])],[(0,[z1,z2,z3,z5,z156,z21,z6]),(0,[z116,z1,z2,z3,z5,z40,z6]),(0,[z1,z2,z57,z3,z42,z5,z6]),(0,[z1,z2,z3,z8,z20,z6,z157])],[(0,[z1,z2,z3,z42,z8,z6,z84]),(0,[z116,z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z42,z5,z6,z27])],[(0,[z28,z1,z2,z3,z5,z158,z6]),(0,[z1,z2,z3,z5,z159,z8,z6]),(0,[z1,z160,z2,z3,z5,z8,z6])],[(0,[z17,z1,z2,z3,z93,z5,z6])],[(0,[z1,z2,z3,z5,z8,z161,z6]),(0,[z1,z44,z2,z57,z3,z5,z6])],[(0,[z162,z1,z2,z3,z5,z8,z6]),(0,[z1,z56,z3,z5,z89,z8,z6]),(0,[z1,z11,z2,z3,z5,z20,z6]),(0,[z1,z2,z3,z5,z8,z163,z6])],[(0,[z1,z2,z3,z33,z5,z10,z6]),(0,[z164,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z89,z40,z8,z6]),(0,[z1,z11,z2,z3,z5,z88,z6]),(1,[z1,z2,z165,z3,z5,z6]),(0,[z166,z17,z1,z2,z3,z5,z6]),(0,[z167,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z29,z8,z6]),(0,[z17,z1,z2,z3,z5,z6,z84]),(0,[z58,z1,z2,z57,z3,z5,z6]),(0,[z116,z1,z2,z3,z5,z18,z6]),(0,[z1,z2,z48,z5,z8,z72,z6]),(0,[z1,z2,z3,z5,z8,z168,z6]),(0,[z1,z2,z3,z42,z8,z18,z6]),(0,[z166,z1,z2,z3,z5,z6,z27])]],
   [[(0,[z1,z2,z3,z4,z42,z8,z6]),(0,[z1,z2,z49,z3,z33,z5,z6]),(0,[z1,z2,z3,z92,z40,z8,z6]),(0,[z131,z1,z2,z3,z5,z169,z6]),(0,[z170,z1,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z171,z8,z6]),(0,[z172,z116,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z59,z5,z8,z6]),(0,[z1,z2,z3,z42,z8,z6,z6])],[(0,[z1,z86,z16,z2,z3,z5,z6]),(0,[z1,z2,z3,z173,z8,z6,z69]),(0,[z1,z2,z3,z174,z5,z8,z6])],[(0,[z116,z1,z25,z2,z3,z5,z6])],[(0,[z1,z2,z3,z175,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z6,z69]),(0,[z1,z2,z176,z3,z5,z8,z6])],[],[(0,[z1,z177,z2,z51,z5,z8,z6]),(0,[z1,z178,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z112,z5,z8,z6]),(0,[z1,z2,z179,z3,z5,z8,z6])],[(0,[z116,z15,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z41,z8,z6]),(0,[z1,z25,z2,z3,z42,z5,z8]),(0,[z1,z180,z2,z3,z5,z8,z6])],[(0,[z137,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z181,z5,z8,z6]),(0,[z1,z2,z152,z49,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z182,z6]),(1,[z1,z183,z2,z3,z5,z6])],[(0,[z1,z2,z3,z184,z5,z21,z6]),(0,[z17,z1,z2,z71,z3,z5,z6]),(0,[z1,z2,z3,z5,z185,z8,z6]),(0,[z1,z44,z2,z3,z42,z5,z8]),(0,[z166,z1,z25,z2,z3,z5,z6]),(0,[z1,z2,z100,z71,z5,z8,z6])],[(0,[z186,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z6,z187]),(1,[z24,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z188,z6])],[(0,[z1,z2,z3,z189,z5,z8,z6])],[(0,[z1,z2,z3,z190,z5,z8,z6]),(0,[z43,z1,z2,z3,z8,z20,z6]),(1,[z1,z191,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z8,z6,z192]),(0,[z1,z2,z3,z5,z21,z97,z6]),(1,[z1,z2,z3,z123,z8,z6]),(0,[z1,z2,z3,z193,z5,z97,z6])],[(0,[z137,z1,z2,z35,z5,z8,z6]),(0,[z116,z1,z2,z3,z5,z10,z6]),(0,[z1,z2,z3,z194,z5,z8,z6]),(1,[z1,z2,z3,z20,z6,z157]),(0,[z1,z2,z3,z5,z6,z6,z27])],[(0,[z1,z2,z3,z5,z8,z6,z195]),(1,[z1,z2,z196,z3,z5,z6]),(0,[z17,z1,z2,z3,z42,z5,z6]),(0,[z1,z3,z5,z8,z97,z6,z70]),(0,[z197,z1,z2,z3,z5,z8,z6])],[(1,[z1,z2,z3,z42,z21,z6]),(0,[z1,z2,z3,z60,z42,z8,z6]),(0,[z1,z2,z3,z5,z89,z8,z6]),(0,[z1,z11,z2,z3,z5,z198,z6]),(0,[z1,z25,z2,z3,z112,z8,z6]),(0,[z1,z2,z57,z3,z42,z8,z6]),(0,[z1,z2,z3,z106,z5,z6,z27])]],
   [[(0,[z1,z2,z3,z93,z5,z41,z6]),(0,[z1,z56,z11,z2,z3,z5,z6]),(1,[z1,z2,z57,z3,z5,z6])],[(0,[z199,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z106,z5,z27])],[(0,[z1,z2,z3,z200,z5,z8,z6]),(0,[z1,z2,z3,z33,z5,z8,z27])],[(0,[z1,z2,z3,z5,z8,z6,z201]),(0,[z1,z2,z3,z202,z5,z8,z6]),(0,[z1,z2,z3,z5,z203,z41,z6]),(0,[z1,z204,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z5,z97,z6,z27]),(0,[z24,z1,z2,z57,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z6,z205])],[(0,[z36,z1,z2,z3,z5,z8,z206]),(1,[z1,z2,z207,z3,z5,z6]),(0,[z1,z2,z3,z5,z21,z72,z6]),(0,[z129,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z71,z3,z101,z8,z6]),(1,[z1,z2,z3,z208,z5,z8]),(0,[z1,z2,z57,z3,z75,z5,z6]),(0,[z1,z2,z209,z3,z5,z8,z6])],[(0,[z17,z151,z1,z2,z3,z5,z6]),(0,[z1,z2,z49,z3,z5,z41,z6])],[(0,[z17,z1,z16,z2,z3,z5,z6]),(0,[z210,z1,z2,z3,z5,z8,z6]),(0,[z7,z1,z2,z3,z5,z21,z6]),(1,[z211,z1,z2,z3,z5,z6]),(1,[z1,z2,z212,z3,z5,z6]),(0,[z1,z25,z2,z3,z128,z8,z6]),(0,[z1,z2,z3,z87,z5,z8,z27])],[(0,[z1,z2,z3,z5,z8,z213,z6]),(0,[z1,z214,z2,z3,z5,z8,z6])],[(1,[z1,z2,z3,z5,z21,z6]),(0,[z9,z1,z2,z3,z215,z8,z6]),(0,[z1,z2,z3,z60,z5,z8,z6]),(1,[z1,z56,z3,z89,z8,z6]),(0,[z1,z2,z57,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z216,z6]),(0,[z1,z2,z217,z3,z5,z8,z6])],[(0,[z1,z218,z2,z3,z5,z21,z6]),(0,[z219,z116,z1,z2,z3,z5,z6]),(0,[z116,z1,z2,z3,z5,z34,z6])],[(0,[z151,z1,z2,z4,z5,z8,z6]),(0,[z1,z11,z2,z2,z3,z5,z6]),(0,[z1,z2,z220,z3,z5,z8,z6])],[(1,[z1,z2,z3,z5,z8,z195]),(0,[z1,z2,z57,z3,z5,z6,z187])],[(0,[z1,z204,z2,z3,z5,z8,z6])],[(0,[z148,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z5,z8,z84,z70]),(0,[z1,z2,z196,z3,z5,z8,z6]),(1,[z17,z1,z2,z3,z20,z6]),(0,[z1,z25,z2,z3,z5,z8,z97]),(1,[z1,z180,z2,z3,z5,z6]),(0,[z1,z2,z221,z3,z5,z8,z6]),(0,[z1,z2,z3,z33,z222,z5,z6])],[(0,[z36,z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z79,z5,z8,z6]),(0,[z1,z2,z223,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z224,z6])],[(0,[z148,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z71,z3,z5,z8,z6]),(0,[z1,z2,z57,z3,z5,z115,z6])]],
   [[(0,[z137,z1,z139,z3,z5,z8,z6]),(0,[z1,z225,z2,z3,z5,z8,z6]),(1,[z1,z2,z26,z5,z8,z69]),(0,[z1,z2,z3,z33,z59,z5,z6]),(0,[z1,z226,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z80,z6]),(0,[z17,z1,z2,z26,z3,z5,z6]),(1,[z1,z2,z3,z227,z5,z6]),(0,[z1,z2,z3,z42,z5,z8,z27]),(0,[z1,z2,z3,z5,z6,z27,z228])],[(0,[z1,z2,z51,z49,z5,z8,z6]),(0,[z1,z2,z51,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z21,z20,z6]),(0,[z1,z2,z3,z5,z229,z8,z6]),(0,[z1,z2,z3,z5,z8,z230,z6]),(0,[z1,z231,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z232])],[(0,[z1,z16,z2,z3,z42,z8,z6]),(0,[z28,z1,z2,z3,z93,z8,z6]),(0,[z1,z2,z3,z233,z5,z8,z6])],[(1,[z9,z2,z3,z5,z8,z10])],[(0,[z1,z2,z234,z3,z5,z8,z6]),(0,[z1,z2,z235,z3,z5,z8,z6]),(0,[z17,z1,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z5,z6,z70,z27]),(0,[z116,z1,z2,z3,z3,z5,z6]),(0,[z1,z2,z3,z42,z8,z6,z69])],[(0,[z1,z2,z3,z5,z8,z236,z6]),(0,[z1,z2,z3,z8,z20,z97,z6]),(1,[z1,z2,z3,z5,z8,z237])],[(0,[z238,z1,z2,z3,z5,z8,z6]),(1,[z28,z2,z3,z92,z8,z6]),(0,[z1,z2,z3,z5,z123,z8,z6]),(0,[z1,z2,z3,z42,z239,z8,z6]),(0,[z1,z2,z3,z239,z5,z8,z6])],[(0,[z1,z2,z57,z49,z3,z5,z6])],[(0,[z137,z1,z2,z3,z114,z8,z6]),(0,[z1,z2,z3,z33,z93,z5,z6]),(0,[z129,z1,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z240,z5,z8,z6]),(1,[z1,z2,z217,z3,z5,z6])],[(0,[z1,z241,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z242,z5,z8,z6]),(0,[z1,z2,z3,z5,z243,z8,z6])],[(0,[z1,z2,z244,z3,z5,z8,z6]),(0,[z107,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z245,z5,z8,z6]),(0,[z1,z177,z2,z3,z5,z246,z6]),(0,[z17,z1,z2,z3,z5,z6,z69]),(0,[z116,z1,z2,z3,z87,z5,z6]),(0,[z1,z2,z3,z42,z8,z6,z187])],[(0,[z1,z16,z2,z3,z5,z8,z6]),(0,[z9,z1,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z247,z6]),(0,[z248,z1,z2,z3,z5,z8,z6]),(0,[z249,z17,z1,z2,z3,z5,z6]),(0,[z1,z2,z26,z3,z5,z8,z72])],[(0,[z1,z2,z3,z33,z5,z6,z84]),(1,[z1,z25,z3,z5,z8,z97]),(0,[z1,z2,z3,z5,z8,z250,z6])],[(0,[z1,z2,z3,z5,z92,z6,z27]),(0,[z17,z1,z2,z3,z5,z8,z6]),(0,[z1,z44,z25,z3,z5,z8,z6]),(0,[z1,z2,z26,z3,z42,z8,z6]),(0,[z1,z2,z3,z8,z20,z72,z6]),(0,[z1,z2,z3,z33,z251,z5,z6])],[(0,[z1,z2,z3,z252,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z8,z20,z6,z70])],[(0,[z17,z1,z2,z3,z5,z6,z187]),(1,[z1,z2,z3,z14,z5,z6]),(0,[z1,z2,z3,z42,z253,z8,z6]),(1,[z1,z2,z3,z33,z5,z27])],[(0,[z1,z2,z3,z254,z5,z8,z6]),(0,[z255,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z57,z3,z38,z5,z6]),(0,[z1,z2,z3,z256,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z21,z6]),(0,[z257,z17,z1,z2,z3,z5,z6]),(0,[z117,z1,z2,z57,z3,z5,z6]),(0,[z1,z2,z258,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z21,z198,z6]),(0,[z148,z1,z2,z3,z5,z41,z6]),(0,[z2,z3,z5,z8,z10,z6,z84]),(0,[z1,z177,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z5,z8,z259,z6]),(1,[z1,z2,z3,z5,z6,z260]),(0,[z1,z2,z261,z3,z42,z8,z6]),(0,[z257,z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z33,z5,z6,z6])],[],[(0,[z1,z2,z262,z3,z5,z8,z6]),(0,[z28,z1,z2,z3,z42,z8,z6]),(0,[z1,z2,z263,z3,z5,z8,z6]),(0,[z9,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z100,z57,z3,z5,z6]),(0,[z116,z1,z2,z3,z264,z5,z6]),(0,[z1,z2,z3,z5,z8,z6,z265])],[(0,[z36,z1,z266,z3,z5,z8,z6]),(0,[z1,z267,z2,z3,z5,z8,z6]),(0,[z1,z2,z268,z3,z5,z8,z6]),(0,[z269,z17,z1,z2,z3,z5,z6]),(0,[z1,z2,z270,z3,z5,z8,z6]),(0,[z1,z2,z3,z106,z5,z8,z27])],[(0,[z116,z1,z2,z3,z93,z5,z6]),(0,[z1,z2,z3,z42,z5,z8,z20]),(0,[z1,z2,z3,z251,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z271]),(0,[z1,z2,z3,z5,z21,z272,z6]),(0,[z1,z2,z3,z5,z273,z8,z6]),(0,[z1,z2,z3,z274,z5,z8,z6])],[(0,[z1,z56,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z275,z5,z8,z6]),(0,[z1,z2,z3,z5,z198,z6,z27]),(0,[z17,z1,z2,z3,z276,z5,z6])],[(1,[z1,z2,z3,z5,z277,z6]),(0,[z1,z2,z3,z8,z67,z6,z69])],[(0,[z1,z2,z3,z93,z8,z20,z6]),(0,[z116,z1,z2,z3,z5,z6,z84]),(0,[z1,z2,z3,z8,z20,z20,z6])],[(0,[z1,z2,z139,z57,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z8,z6]),(0,[z278,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z215,z8,z6]),(0,[z1,z44,z11,z2,z3,z5,z6]),(0,[z1,z25,z2,z57,z3,z5,z6]),(0,[z1,z2,z261,z3,z5,z8,z6])],[(0,[z17,z1,z2,z49,z3,z5,z6]),(0,[z1,z2,z100,z3,z5,z21,z6]),(0,[z1,z279,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z280,z8,z6])],[(0,[z28,z1,z2,z3,z5,z8,z6]),(0,[z43,z1,z2,z3,z281,z8,z6])]],
   [[(0,[z282,z1,z2,z3,z5,z8,z6]),(0,[z1,z283,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z284]),(0,[z1,z204,z56,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z285]),(0,[z286,z1,z2,z3,z42,z8,z6])],[(0,[z1,z2,z49,z3,z8,z20,z6])],[(0,[z1,z2,z3,z5,z114,z8,z6]),(0,[z151,z1,z2,z3,z5,z287,z6]),(1,[z1,z2,z3,z5,z288,z6]),(0,[z1,z2,z3,z42,z87,z8,z6])],[(0,[z1,z2,z3,z289,z5,z8,z6]),(0,[z1,z2,z3,z5,z290,z8,z6]),(0,[z1,z2,z3,z5,z8,z291,z6])],[(1,[z1,z2,z3,z42,z41,z6]),(0,[z1,z2,z3,z5,z8,z6,z292])],[(0,[z1,z2,z139,z3,z5,z21,z6]),(0,[z1,z25,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z293,z5,z8,z6]),(0,[z116,z1,z2,z71,z3,z5,z6]),(0,[z1,z2,z152,z57,z3,z5,z6])],[(1,[z1,z11,z3,z5,z198,z6]),(0,[z1,z2,z3,z101,z5,z6,z27]),(0,[z1,z2,z26,z3,z5,z294,z6]),(0,[z1,z2,z48,z3,z33,z5,z6]),(0,[z1,z2,z3,z42,z59,z8,z6])],[(0,[z15,z1,z2,z3,z5,z295,z6]),(1,[z36,z2,z4,z5,z8,z6]),(0,[z131,z1,z2,z3,z5,z6,z27]),(0,[z1,z44,z2,z3,z5,z21,z6]),(0,[z148,z116,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z128,z8,z6]),(0,[z1,z2,z3,z5,z40,z6,z27]),(0,[z1,z2,z3,z296,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z297]),(0,[z1,z2,z3,z173,z5,z8,z6])],[(0,[z1,z2,z298,z3,z5,z8,z6]),(0,[z17,z1,z2,z3,z38,z5,z6])],[(0,[z299,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z300,z5,z6]),(0,[z1,z2,z3,z5,z8,z301,z6]),(0,[z1,z2,z100,z101,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z302,z6]),(0,[z303,z1,z2,z3,z5,z6,z27])],[(0,[z58,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z53,z5,z6,z27]),(0,[z1,z2,z47,z3,z33,z5,z6])],[(0,[z1,z2,z304,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z5,z8,z10]),(0,[z116,z1,z2,z3,z42,z5,z6])],[(1,[z110,z1,z2,z3,z5,z6]),(0,[z1,z2,z51,z3,z5,z288,z6]),(0,[z1,z2,z3,z305,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z306,z6])],[(0,[z1,z204,z2,z3,z38,z8,z6]),(0,[z1,z307,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z42,z308,z6])],[(0,[z309,z1,z2,z3,z5,z8,z6]),(0,[z1,z204,z2,z3,z89,z8,z6]),(0,[z1,z11,z2,z3,z5,z6,z27]),(1,[z1,z2,z3,z5,z6,z310]),(0,[z1,z2,z3,z5,z8,z311,z6]),(0,[z1,z2,z3,z312,z5,z8,z6])],[(0,[z1,z2,z313,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z93,z8,z6]),(0,[z1,z56,z2,z3,z5,z41,z6]),(0,[z17,z1,z2,z3,z101,z5,z6]),(0,[z1,z2,z3,z5,z8,z6,z260])]],
   [[(0,[z1,z2,z3,z314,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z115,z6])],[(0,[z1,z315,z2,z3,z5,z8,z6]),(1,[z1,z11,z2,z3,z5,z6]),(1,[z58,z1,z2,z3,z53,z6])],[(0,[z1,z1,z2,z3,z5,z8,z6]),(0,[z116,z151,z1,z2,z3,z5,z6]),(0,[z1,z316,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z10,z70])],[(0,[z116,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z317,z8,z6]),(1,[z1,z177,z51,z5,z8,z6]),(1,[z1,z231,z2,z3,z5,z6]),(0,[z1,z2,z3,z318,z5,z8,z6])],[(0,[z1,z319,z2,z3,z5,z8,z6]),(0,[z320,z1,z2,z3,z5,z8,z6]),(1,[z99,z1,z2,z3,z5,z6]),(0,[z24,z1,z11,z2,z3,z5,z6]),(0,[z1,z180,z2,z57,z3,z5,z6])],[(0,[z137,z1,z2,z57,z3,z5,z6]),(0,[z129,z1,z2,z3,z8,z20,z6]),(0,[z1,z11,z2,z3,z5,z321,z6]),(0,[z1,z2,z3,z322,z5,z8,z6])],[(0,[z1,z2,z3,z59,z5,z21,z6]),(0,[z1,z2,z3,z5,z323,z8,z6]),(0,[z9,z1,z2,z3,z33,z5,z6]),(0,[z324,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z88,z6,z27]),(1,[z1,z2,z3,z5,z308,z6])],[(0,[z1,z2,z3,z3,z5,z8,z6]),(0,[z325,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z8,z168,z20,z6])],[(0,[z1,z2,z3,z5,z8,z326,z6]),(0,[z1,z2,z3,z5,z327,z8,z6]),(0,[z328,z1,z2,z3,z5,z8,z6])],[(1,[z1,z329,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z330,z8,z6]),(0,[z1,z11,z3,z5,z8,z198,z6]),(0,[z1,z2,z3,z33,z5,z6,z69]),(0,[z1,z2,z3,z33,z91,z8,z6])],[],[(1,[z1,z2,z3,z5,z8,z331]),(0,[z131,z28,z2,z3,z5,z8,z6]),(0,[z1,z2,z48,z3,z5,z41,z6]),(0,[z1,z2,z3,z332,z5,z41,z6]),(0,[z43,z17,z1,z2,z3,z5,z6]),(0,[z1,z2,z57,z3,z5,z149,z6]),(1,[z1,z25,z2,z3,z42,z8])],[(0,[z1,z86,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z21,z6]),(0,[z1,z2,z3,z333,z5,z8,z6]),(0,[z1,z2,z26,z3,z5,z8,z69]),(0,[z1,z2,z3,z8,z250,z20,z6]),(0,[z1,z2,z3,z8,z18,z20,z6]),(0,[z1,z2,z3,z33,z5,z8,z6])],[(0,[z1,z2,z3,z35,z5,z8,z6]),(0,[z137,z1,z2,z3,z5,z21,z6]),(1,[z1,z2,z3,z5,z334,z6]),(0,[z1,z2,z3,z5,z8,z288,z6]),(0,[z1,z2,z3,z5,z8,z6,z335]),(0,[z1,z2,z3,z5,z8,z6,z336]),(0,[z1,z2,z3,z101,z5,z337,z6]),(1,[z1,z2,z3,z5,z6,z338]),(0,[z1,z2,z3,z5,z6,z339,z27])],[(0,[z340,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z21,z6,z228]),(0,[z1,z2,z341,z3,z8,z20,z6])],[(0,[z151,z1,z2,z3,z42,z8,z6]),(1,[z1,z2,z3,z173,z8,z6]),(0,[z1,z2,z3,z33,z5,z6,z187])]],
   [[(0,[z107,z1,z2,z3,z5,z41,z6]),(0,[z1,z2,z342,z3,z5,z8,z6])],[(0,[z1,z2,z3,z38,z93,z8,z6]),(0,[z1,z2,z3,z93,z40,z8,z6]),(0,[z1,z2,z3,z343,z5,z89,z8]),(0,[z1,z2,z3,z5,z8,z344,z6]),(0,[z1,z2,z5,z88,z8,z115,z6]),(0,[z1,z2,z3,z5,z8,z345,z6])],[(0,[z1,z11,z2,z3,z5,z10,z6]),(0,[z1,z2,z3,z5,z346,z8,z6]),(0,[z116,z1,z2,z3,z42,z8,z6]),(0,[z347,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z42,z8,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z348,z5,z8,z6]),(0,[z1,z349,z2,z3,z5,z8,z6]),(0,[z350,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z351,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z352])],[(0,[z107,z1,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z5,z8,z84])],[(0,[z1,z2,z3,z5,z89,z21,z6]),(0,[z82,z1,z11,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z8,z353,z6]),(0,[z1,z2,z57,z57,z3,z5,z6]),(0,[z58,z1,z2,z3,z53,z5,z6])],[(0,[z1,z354,z2,z3,z5,z8,z6]),(0,[z17,z1,z2,z48,z3,z5,z6]),(0,[z1,z2,z3,z5,z355,z8,z6]),(0,[z1,z44,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z33,z356,z5,z6])],[(0,[z151,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z357,z5,z8,z6]),(0,[z116,z1,z2,z3,z5,z6,z69])],[(0,[z1,z2,z3,z5,z8,z6,z310])],[(1,[z1,z2,z152,z3,z5,z6]),(0,[z1,z2,z3,z358,z5,z8,z6]),(0,[z1,z2,z3,z359,z5,z6,z84]),(0,[z1,z204,z2,z57,z3,z5,z6]),(0,[z17,z1,z2,z165,z3,z5,z6]),(0,[z1,z2,z3,z53,z8,z34,z6])],[(0,[z9,z1,z2,z3,z5,z41,z6]),(0,[z116,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z5,z8,z6]),(0,[z1,z2,z3,z5,z20,z6,z157])],[(0,[z1,z2,z3,z208,z5,z8,z6])],[(0,[z360,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z71,z57,z3,z5,z6]),(0,[z1,z2,z3,z5,z361,z40,z6]),(0,[z1,z2,z3,z362,z5,z72,z6])],[(0,[z363,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z57,z3,z5,z21,z6]),(0,[z1,z11,z2,z3,z5,z34,z6]),(0,[z116,z1,z2,z3,z5,z6,z187])],[(0,[z1,z2,z364,z3,z5,z8,z6])]],
   [[(0,[z43,z1,z2,z51,z5,z8,z6]),(0,[z17,z365,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z69,z27])],[(0,[z166,z1,z2,z3,z5,z8,z6]),(0,[z17,z1,z2,z3,z5,z149,z6])],[(0,[z1,z2,z3,z5,z8,z6,z366]),(0,[z1,z204,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z42,z8,z115,z6]),(0,[z116,z1,z2,z3,z59,z5,z6])],[(0,[z1,z2,z3,z5,z21,z6,z27]),(0,[z1,z2,z3,z208,z5,z40,z8]),(0,[z1,z2,z3,z8,z20,z367,z6])],[(0,[z129,z1,z2,z3,z5,z50,z6]),(0,[z129,z2,z3,z5,z8,z6,z84]),(0,[z1,z2,z368,z3,z5,z8,z6]),(0,[z1,z2,z3,z369,z5,z8,z6]),(0,[z1,z2,z3,z8,z370,z20,z6])],[(0,[z1,z2,z3,z5,z8,z371,z6]),(0,[z1,z2,z71,z3,z5,z21,z6]),(0,[z1,z2,z3,z38,z5,z78,z6]),(1,[z1,z44,z3,z5,z8,z70]),(0,[z372,z116,z1,z2,z3,z5,z6]),(0,[z1,z373,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z33,z38,z5,z6]),(0,[z1,z374,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z375,z5,z8,z6]),(0,[z1,z2,z376,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z377,z8,z6]),(0,[z1,z2,z3,z5,z8,z97,z84]),(0,[z1,z2,z3,z5,z8,z6,z378]),(0,[z379,z1,z2,z3,z5,z8,z6]),(0,[z116,z1,z2,z3,z5,z380,z6])],[(0,[z381,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z334,z6]),(0,[z382,z1,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z8,z383,z6]),(0,[z1,z2,z384,z3,z5,z8,z6]),(0,[z17,z1,z2,z3,z5,z115,z6]),(0,[z1,z2,z3,z5,z8,z6,z338]),(1,[z1,z2,z3,z5,z6,z157])],[(0,[z1,z2,z385,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z21,z18,z6]),(1,[z1,z2,z3,z8,z20,z6])],[(0,[z1,z16,z2,z57,z3,z5,z6]),(0,[z1,z25,z2,z3,z5,z41,z6]),(0,[z1,z191,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z149,z8,z20,z6]),(0,[z1,z2,z26,z3,z5,z8,z6])],[(0,[z116,z1,z2,z49,z3,z5,z6]),(0,[z1,z56,z2,z3,z8,z20,z6]),(0,[z1,z386,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z33,z5,z6])],[(0,[z1,z44,z2,z3,z5,z41,z6]),(0,[z1,z387,z2,z3,z5,z8,z6]),(0,[z17,z1,z2,z57,z3,z5,z6])],[(0,[z1,z2,z3,z38,z5,z8,z6]),(0,[z1,z2,z3,z33,z101,z5,z6]),(0,[z58,z1,z2,z3,z53,z8,z6])],[(0,[z1,z2,z3,z5,z388,z8,z6]),(0,[z1,z25,z11,z2,z3,z5,z6])],[(0,[z15,z1,z2,z3,z5,z6,z27]),(0,[z58,z1,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z8,z72,z84]),(1,[z1,z2,z3,z42,z8,z18])]],
   [[(1,[z166,z1,z2,z3,z5,z6]),(0,[z389,z1,z2,z3,z5,z8,z6])],[(0,[z390,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z391,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z326,z6]),(0,[z1,z2,z3,z5,z392,z8,z6]),(0,[z1,z2,z3,z5,z393,z8,z6])],[(0,[z1,z16,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z8,z6,z394]),(1,[z1,z2,z3,z106,z8,z20])],[(0,[z1,z11,z2,z3,z5,z92,z6]),(0,[z1,z2,z51,z3,z8,z20,z6]),(0,[z58,z1,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z395,z5,z8,z6])],[(1,[z1,z2,z3,z147,z5,z6]),(0,[z17,z1,z2,z3,z5,z21,z6])],[(0,[z36,z1,z2,z4,z5,z8,z6]),(0,[z1,z2,z51,z3,z33,z5,z6]),(0,[z116,z1,z2,z3,z38,z5,z6]),(0,[z1,z2,z270,z57,z3,z5,z6]),(0,[z1,z396,z2,z3,z42,z8,z6])],[(0,[z1,z11,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z397,z5,z8,z6]),(0,[z43,z1,z177,z3,z5,z8,z6])],[(0,[z36,z1,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z5,z21,z10,z6]),(0,[z1,z2,z48,z3,z8,z20,z6]),(0,[z1,z2,z3,z5,z8,z6,z68]),(0,[z1,z2,z3,z398,z42,z8,z6])],[(0,[z1,z399,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z400]),(0,[z1,z2,z165,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z70])],[(1,[z1,z2,z3,z5,z344,z6]),(0,[z1,z2,z48,z3,z401,z8,z6]),(0,[z1,z2,z3,z8,z34,z20,z6]),(0,[z1,z2,z3,z402,z5,z8,z6])],[(0,[z36,z2,z3,z4,z5,z8,z6]),(0,[z1,z403,z2,z3,z5,z8,z6]),(0,[z1,z2,z404,z3,z5,z8,z6]),(0,[z405,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z406,z6]),(0,[z407,z1,z2,z3,z5,z8,z6])],[(0,[z107,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z143,z60,z5,z6]),(0,[z116,z1,z2,z3,z101,z5,z6]),(0,[z286,z1,z2,z3,z5,z8,z6])],[(0,[z28,z1,z2,z57,z3,z5,z6])],[(0,[z107,z1,z2,z3,z33,z5,z6]),(1,[z116,z1,z2,z57,z5,z6]),(0,[z1,z396,z2,z3,z5,z8,z6])],[(0,[z1,z2,z408,z3,z5,z8,z6])]],
   [[(0,[z36,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z41,z6]),(0,[z1,z11,z2,z3,z5,z40,z6]),(0,[z1,z2,z3,z409,z42,z8,z6])],[(0,[z1,z410,z2,z3,z5,z8,z6]),(0,[z2,z3,z5,z41,z8,z21,z6]),(0,[z1,z11,z2,z3,z5,z6,z84]),(0,[z1,z2,z3,z5,z8,z6,z411]),(0,[z1,z2,z26,z3,z42,z5,z8]),(0,[z1,z2,z3,z106,z5,z8,z20])],[(0,[z137,z1,z2,z3,z5,z41,z6]),(1,[z1,z2,z100,z101,z8,z6]),(0,[z58,z116,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z308,z8,z6])],[(0,[z1,z2,z3,z5,z21,z34,z6]),(0,[z1,z2,z3,z5,z8,z6,z157])],[(0,[z1,z2,z3,z42,z41,z8,z6]),(1,[z17,z1,z11,z3,z5,z6]),(0,[z1,z2,z3,z412,z5,z8,z6]),(1,[z1,z2,z3,z5,z8,z68]),(1,[z1,z2,z3,z120,z20,z6])],[(0,[z137,z1,z16,z3,z5,z8,z6]),(0,[z28,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z8,z413,z6]),(0,[z116,z1,z2,z3,z5,z76,z6])],[(0,[z137,z1,z11,z2,z3,z5,z6]),(0,[z414,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z5,z8,z187])],[(0,[z9,z1,z2,z3,z8,z20,z6]),(0,[z1,z11,z2,z3,z5,z18,z6]),(0,[z415,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z416,z42,z8,z6])],[(0,[z1,z2,z3,z5,z8,z417,z6]),(1,[z1,z2,z3,z5,z50,z6]),(1,[z1,z2,z57,z3,z42,z6])],[(0,[z1,z2,z3,z359,z5,z8,z6])],[(0,[z1,z2,z51,z3,z5,z41,z6]),(0,[z1,z2,z3,z418,z5,z89,z8]),(0,[z1,z11,z2,z71,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z12,z6]),(0,[z1,z2,z3,z8,z419,z6,z70]),(0,[z1,z2,z3,z5,z8,z237,z6]),(0,[z420,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z421,z3,z5,z8,z6])],[(0,[z1,z2,z3,z101,z93,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z422]),(0,[z1,z2,z3,z42,z38,z8,z6])],[(0,[z131,z1,z2,z3,z93,z8,z6]),(0,[z1,z177,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z42,z89,z8,z6]),(0,[z1,z2,z3,z5,z423,z89,z6]),(0,[z1,z424,z2,z3,z5,z8,z6]),(0,[z257,z1,z2,z3,z42,z8,z6])],[(0,[z1,z2,z3,z5,z8,z425,z6])],[(0,[z43,z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z33,z5,z149,z6]),(0,[z1,z2,z100,z3,z8,z20,z6])]],
   [[(0,[z137,z15,z2,z3,z5,z8,z6]),(0,[z137,z1,z2,z3,z5,z8,z331]),(0,[z426,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z92,z8,z6]),(0,[z1,z2,z3,z5,z8,z370,z6]),(0,[z1,z11,z2,z3,z42,z5,z6]),(0,[z1,z2,z3,z427,z5,z8,z6]),(1,[z1,z2,z57,z5,z115,z6])],[(0,[z186,z1,z2,z139,z3,z5,z6]),(0,[z428,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z97,z10]),(0,[z1,z2,z100,z3,z33,z5,z6]),(0,[z7,z116,z1,z2,z3,z5,z6]),(0,[z116,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z126,z33,z5,z6])],[(0,[z15,z1,z2,z3,z5,z377,z6]),(0,[z1,z2,z3,z4,z5,z21,z6]),(0,[z1,z429,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z430,z6]),(0,[z1,z2,z431,z3,z5,z8,z6])],[(0,[z1,z2,z3,z432,z5,z8,z6]),(0,[z1,z2,z3,z42,z101,z8,z6]),(1,[z116,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z87,z5,z8,z6])],[(0,[z1,z2,z3,z106,z5,z8,z10]),(0,[z116,z1,z2,z48,z3,z5,z6]),(0,[z1,z2,z48,z3,z174,z8,z6]),(0,[z433,z1,z2,z3,z5,z8,z6]),(0,[z1,z191,z2,z3,z33,z5,z6])],[],[(0,[z257,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z139,z3,z8,z20,z6]),(0,[z129,z1,z2,z3,z5,z6,z27]),(0,[z1,z25,z2,z3,z8,z20,z6]),(0,[z1,z2,z434,z3,z5,z8,z6]),(0,[z1,z2,z3,z33,z5,z115,z6])],[(0,[z1,z2,z3,z5,z435,z8,z6]),(0,[z211,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z436,z6]),(0,[z116,z437,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z6,z438])],[(0,[z1,z2,z139,z3,z33,z5,z6]),(0,[z1,z11,z16,z2,z3,z5,z6]),(0,[z1,z2,z439,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z440,z8,z6]),(0,[z1,z1,z2,z3,z5,z21,z6]),(0,[z1,z44,z2,z3,z8,z20,z6]),(0,[z1,z25,z2,z3,z33,z5,z6]),(0,[z441,z1,z2,z3,z5,z8,z6])],[(0,[z17,z129,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z72,z10]),(0,[z1,z442,z2,z3,z5,z8,z6])],[(0,[z17,z107,z1,z2,z3,z5,z6]),(0,[z443,z1,z2,z3,z5,z8,z6]),(0,[z129,z1,z2,z3,z5,z444,z6]),(0,[z1,z177,z2,z60,z5,z8,z6]),(0,[z445,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z432,z5,z40,z8]),(0,[z1,z2,z3,z446,z5,z8,z6]),(0,[z1,z2,z3,z42,z252,z8,z6])],[(0,[z1,z2,z3,z5,z8,z447,z6]),(0,[z1,z204,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z149,z8,z6]),(0,[z58,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z5,z6,z27,z187])],[(0,[z1,z2,z3,z202,z5,z21,z6]),(0,[z448,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z449])],[(0,[z58,z1,z2,z3,z33,z5,z6])],[(0,[z1,z2,z3,z5,z8,z6,z450]),(0,[z116,z1,z2,z3,z5,z149,z6]),(0,[z1,z2,z3,z451,z5,z8,z6]),(0,[z1,z183,z2,z3,z33,z5,z6])],[(0,[z1,z2,z3,z14,z5,z6,z70]),(0,[z452,z1,z2,z3,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z5,z453,z8,z6]),(0,[z1,z2,z454,z3,z5,z8,z6]),(0,[z131,z1,z2,z3,z42,z8,z6]),(0,[z148,z17,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z60,z5,z21,z6]),(0,[z148,z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z5,z8,z455,z6])],[(0,[z1,z2,z3,z33,z5,z21,z6]),(0,[z1,z2,z3,z5,z8,z6,z456])],[],[(0,[z1,z2,z3,z5,z457,z8,z6])],[(1,[z1,z2,z3,z359,z5,z6]),(0,[z1,z458,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z459,z6]),(0,[z1,z2,z3,z5,z460,z8,z6]),(0,[z116,z1,z2,z3,z5,z115,z6])],[(1,[z1,z2,z3,z5,z461,z6]),(0,[z151,z1,z2,z57,z3,z5,z6]),(0,[z1,z2,z3,z5,z21,z6,z84]),(0,[z1,z2,z100,z3,z5,z41,z6])],[(1,[z1,z2,z3,z5,z8,z37]),(0,[z1,z11,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z40,z8,z20,z6]),(0,[z1,z2,z3,z59,z8,z20,z6])],[(0,[z1,z2,z3,z5,z461,z8,z6]),(0,[z1,z2,z3,z5,z41,z30,z6]),(0,[z1,z2,z3,z101,z5,z8,z6])],[(0,[z131,z1,z2,z3,z5,z8,z6]),(0,[z116,z1,z2,z57,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z411]),(0,[z1,z2,z3,z462,z5,z8,z6])],[(0,[z17,z1,z177,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z5,z6,z310]),(0,[z90,z116,z1,z2,z3,z5,z6])],[(1,[z1,z2,z3,z5,z8,z450]),(0,[z1,z2,z3,z5,z229,z21,z6]),(1,[z1,z2,z3,z193,z5,z6])],[(0,[z1,z2,z3,z8,z115,z20,z6]),(0,[z1,z2,z3,z463,z5,z8,z6])],[(0,[z1,z2,z139,z3,z5,z41,z6]),(0,[z1,z2,z3,z106,z5,z8,z84]),(0,[z17,z1,z11,z2,z3,z5,z6]),(0,[z1,z11,z2,z3,z5,z6,z69]),(0,[z116,z1,z66,z2,z3,z5,z6])],[(0,[z137,z1,z2,z3,z8,z20,z6]),(0,[z151,z1,z2,z49,z5,z8,z6]),(0,[z151,z1,z2,z3,z5,z21,z6]),(1,[z1,z2,z71,z40,z8,z6]),(1,[z1,z2,z3,z401,z8,z6])],[(1,[z1,z2,z3,z8,z464,z6])]],
   [[(0,[z137,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z358,z5,z21,z6]),(0,[z465,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z42,z5,z21,z6]),(0,[z116,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z42,z8,z21,z6]),(0,[z1,z2,z3,z5,z8,z97,z6]),(1,[z466,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z264,z5,z8,z6])],[(0,[z1,z25,z2,z3,z5,z8,z70]),(0,[z1,z2,z3,z5,z467,z8,z6])],[(0,[z1,z2,z3,z5,z41,z468,z6]),(0,[z1,z11,z2,z3,z87,z5,z6]),(0,[z17,z1,z2,z100,z3,z5,z6]),(0,[z1,z2,z3,z53,z59,z5,z6])],[(0,[z1,z44,z2,z3,z5,z8,z70]),(0,[z1,z2,z71,z5,z40,z8,z6]),(0,[z1,z2,z100,z3,z40,z8,z6]),(0,[z1,z2,z3,z106,z5,z8,z6])],[(0,[z1,z2,z152,z3,z5,z41,z6]),(1,[z1,z2,z376,z3,z5,z6])],[(0,[z17,z1,z2,z139,z3,z5,z6]),(0,[z1,z2,z3,z469,z5,z8,z6]),(0,[z470,z1,z2,z3,z5,z8,z6]),(0,[z219,z1,z2,z3,z5,z6,z27])],[(0,[z1,z2,z3,z471,z5,z8,z6]),(0,[z1,z11,z2,z3,z59,z5,z6]),(0,[z1,z472,z2,z3,z5,z8,z6])],[(0,[z36,z1,z2,z3,z254,z8,z6]),(0,[z1,z2,z3,z5,z8,z473,z6]),(0,[z1,z2,z26,z57,z3,z5,z6])],[(1,[z1,z2,z3,z5,z474,z6]),(0,[z1,z475,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z72,z6])],[(0,[z1,z2,z476,z3,z5,z8,z6]),(0,[z9,z2,z3,z5,z8,z10,z6])],[(0,[z1,z477,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z478,z5,z8,z6]),(0,[z1,z2,z3,z88,z8,z20,z6])],[(1,[z1,z2,z3,z5,z479,z6]),(0,[z1,z2,z3,z5,z277,z8,z6]),(0,[z1,z2,z3,z5,z72,z6,z480])],[(1,[z1,z2,z3,z104,z8,z6]),(0,[z131,z1,z2,z3,z5,z8,z80]),(0,[z1,z2,z3,z5,z8,z481,z6]),(0,[z1,z2,z57,z3,z53,z5,z6]),(0,[z1,z2,z3,z8,z482,z6,z27])],[(0,[z28,z1,z11,z2,z3,z5,z6]),(1,[z148,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z59,z5,z41,z6])],[(0,[z1,z2,z3,z483,z5,z8,z6]),(0,[z1,z2,z57,z3,z8,z20,z6]),(0,[z1,z2,z3,z5,z484,z8,z6]),(0,[z1,z2,z485,z3,z5,z8,z6])]],
   [[(0,[z1,z486,z2,z3,z5,z8,z6]),(0,[z1,z11,z2,z49,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z487,z6]),(0,[z28,z2,z3,z5,z92,z8,z6]),(0,[z1,z11,z2,z3,z93,z5,z6]),(0,[z1,z2,z3,z93,z5,z6,z27]),(0,[z1,z2,z26,z3,z5,z21,z6]),(0,[z1,z2,z57,z3,z5,z413,z6]),(0,[z1,z2,z3,z8,z20,z6,z27])],[(0,[z1,z2,z3,z300,z5,z10,z6]),(0,[z1,z2,z57,z3,z33,z5,z6]),(0,[z1,z2,z3,z488,z5,z6,z69])],[(1,[z186,z1,z2,z3,z5,z6]),(0,[z17,z28,z1,z2,z3,z5,z6]),(0,[z1,z2,z489,z3,z5,z8,z6])],[(0,[z1,z2,z3,z398,z5,z8,z6]),(0,[z1,z2,z3,z38,z5,z21,z6]),(0,[z1,z490,z2,z3,z5,z8,z6]),(0,[z1,z3,z38,z5,z89,z8,z6]),(0,[z1,z204,z2,z3,z8,z20,z6]),(0,[z1,z2,z101,z5,z40,z8,z6]),(0,[z142,z116,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z41,z41,z6])],[(1,[z1,z2,z3,z5,z295,z6]),(0,[z1,z2,z49,z3,z5,z6,z27]),(0,[z1,z204,z2,z3,z33,z5,z6]),(0,[z491,z17,z1,z2,z3,z5,z6])],[(0,[z1,z2,z4,z60,z5,z8,z6]),(0,[z110,z17,z1,z2,z3,z5,z6]),(0,[z1,z44,z2,z3,z5,z436,z6]),(0,[z1,z2,z71,z3,z8,z20,z6]),(0,[z1,z2,z3,z63,z5,z8,z6])],[(0,[z1,z2,z3,z4,z5,z41,z6]),(0,[z1,z492,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z493]),(0,[z1,z2,z3,z5,z8,z20,z6])],[(0,[z494,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z71,z3,z33,z5,z6])],[(0,[z1,z2,z3,z495,z5,z8,z6]),(0,[z1,z2,z3,z5,z401,z8,z6]),(1,[z1,z2,z3,z174,z8,z6])],[(0,[z1,z2,z3,z5,z8,z331,z6]),(0,[z1,z2,z3,z5,z8,z464,z6]),(0,[z1,z11,z2,z3,z38,z5,z6]),(0,[z1,z25,z3,z5,z8,z97,z6]),(0,[z1,z2,z3,z5,z496,z8,z6]),(0,[z1,z497,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z498,z8,z6,z27])],[(0,[z1,z2,z3,z5,z499,z8,z6])],[(0,[z1,z2,z3,z409,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z500,z6]),(0,[z1,z2,z3,z5,z89,z41,z6])],[(0,[z36,z1,z2,z57,z3,z5,z6])],[(1,[z1,z2,z3,z5,z501,z6]),(0,[z1,z177,z51,z3,z5,z8,z6])]],
   [[(0,[z148,z107,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z361,z8,z6]),(0,[z1,z2,z3,z120,z8,z20,z6]),(0,[z1,z2,z3,z120,z5,z20,z6])],[(0,[z1,z2,z3,z5,z8,z502,z6]),(0,[z1,z11,z2,z3,z101,z5,z6])],[(0,[z1,z2,z3,z5,z21,z6,z69]),(0,[z249,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z482,z6,z27])],[(0,[z1,z2,z3,z416,z5,z8,z6]),(0,[z17,z1,z2,z3,z53,z5,z6]),(0,[z1,z2,z48,z3,z106,z5,z8])],[(0,[z1,z2,z3,z5,z8,z474,z6]),(0,[z1,z2,z3,z8,z20,z10,z6]),(0,[z1,z2,z3,z503,z5,z8,z6])],[(0,[z1,z16,z2,z3,z33,z5,z6]),(1,[z1,z2,z3,z41,z20,z6]),(1,[z1,z2,z3,z20,z6,z27])],[(0,[z36,z1,z2,z49,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z94,z6]),(0,[z36,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z60,z5,z41,z6]),(0,[z1,z2,z57,z3,z5,z41,z6]),(0,[z116,z129,z1,z2,z3,z5,z6]),(0,[z1,z44,z3,z5,z8,z6,z70])],[(0,[z16,z2,z139,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z479,z6]),(0,[z1,z2,z504,z3,z5,z8,z6]),(0,[z116,z107,z1,z2,z3,z5,z6]),(0,[z1,z86,z2,z3,z5,z41,z6]),(0,[z9,z1,z2,z3,z5,z474,z6]),(0,[z17,z1,z2,z3,z33,z5,z6])],[(0,[z137,z116,z1,z2,z3,z5,z6]),(0,[z15,z1,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z5,z104,z8,z6]),(0,[z1,z2,z3,z5,z21,z6,z187]),(0,[z1,z2,z3,z5,z10,z6,z505]),(0,[z1,z2,z3,z506,z5,z8,z6]),(1,[z1,z2,z3,z42,z103,z6])],[(1,[z15,z16,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z444,z6]),(0,[z1,z177,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z101,z38,z8,z6]),(0,[z1,z2,z3,z5,z8,z198,z6]),(0,[z1,z2,z3,z5,z8,z6,z480])],[(0,[z1,z204,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z41,z97,z6]),(0,[z1,z2,z3,z101,z89,z8,z6]),(0,[z1,z2,z3,z5,z430,z8,z6]),(0,[z1,z2,z3,z5,z6,z27,z96])],[(0,[z1,z86,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z507,z8,z6]),(1,[z1,z2,z47,z3,z5,z6])],[(0,[z2,z3,z93,z5,z92,z8,z6]),(0,[z1,z2,z508,z3,z5,z8,z6]),(0,[z1,z509,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z510,z5,z8,z6])],[(0,[z1,z2,z71,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z511,z8,z6]),(0,[z269,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z498,z6,z27]),(0,[z1,z2,z3,z222,z5,z8,z6])],[(0,[z1,z2,z138,z3,z5,z8,z6]),(0,[z1,z2,z3,z289,z8,z6,z70]),(0,[z1,z2,z3,z5,z8,z512,z6])],[(0,[z1,z2,z3,z106,z5,z8,z187])]],
   [[(0,[z1,z2,z3,z5,z8,z295,z6]),(0,[z1,z2,z3,z513,z5,z8,z6]),(1,[z1,z2,z3,z281,z8,z6])],[(1,[z129,z2,z3,z5,z8,z84])],[(0,[z1,z2,z514,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z72,z6]),(0,[z1,z2,z57,z3,z60,z5,z6]),(0,[z99,z1,z2,z3,z5,z8,z6]),(0,[z1,z349,z11,z2,z3,z5,z6])],[],[(0,[z1,z16,z3,z60,z5,z8,z6]),(0,[z1,z2,z3,z515,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z6,z70]),(0,[z257,z1,z2,z57,z3,z5,z6]),(0,[z1,z2,z351,z57,z3,z5,z6]),(0,[z1,z2,z57,z3,z106,z5,z6]),(0,[z1,z516,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z517]),(0,[z1,z2,z3,z5,z518,z8,z6]),(1,[z1,z2,z3,z87,z5,z27])],[(0,[z1,z2,z3,z5,z8,z6,z206]),(0,[z1,z354,z11,z2,z3,z5,z6]),(0,[z1,z11,z2,z26,z3,z5,z6]),(0,[z1,z2,z57,z3,z5,z6,z338])],[(0,[z151,z1,z11,z2,z3,z5,z6]),(0,[z116,z1,z177,z2,z3,z5,z6])],[(0,[z28,z1,z2,z3,z33,z5,z6]),(1,[z1,z2,z3,z5,z6,z228]),(1,[z382,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z87,z5,z21,z6]),(0,[z1,z2,z26,z48,z5,z8,z6])],[(0,[z519,z1,z2,z3,z5,z8,z6]),(0,[z1,z16,z2,z3,z5,z41,z6]),(0,[z1,z11,z2,z3,z5,z6,z74]),(0,[z116,z1,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z520,z5,z8,z6]),(1,[z1,z2,z26,z3,z42,z8])],[(1,[z1,z2,z3,z521,z8,z6]),(0,[z522,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z155,z5,z8,z6]),(0,[z1,z2,z71,z3,z40,z8,z6]),(0,[z523,z1,z2,z3,z5,z8,z6])],[(0,[z17,z1,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z521,z8,z6,z84]),(0,[z1,z2,z3,z343,z5,z8,z6]),(0,[z1,z2,z57,z3,z5,z97,z6]),(0,[z1,z2,z3,z5,z40,z8,z6]),(0,[z1,z2,z3,z5,z524,z8,z6])],[(1,[z151,z2,z49,z5,z8,z6]),(0,[z1,z2,z3,z5,z10,z6,z27]),(0,[z1,z2,z525,z3,z5,z8,z6]),(1,[z1,z2,z48,z3,z42,z8]),(0,[z1,z2,z3,z5,z482,z6,z27])],[(0,[z303,z1,z2,z3,z5,z8,z6])],[(0,[z116,z1,z2,z57,z5,z8,z6]),(0,[z1,z2,z3,z53,z5,z8,z6]),(0,[z1,z2,z3,z42,z5,z308,z6])]],
   [[(0,[z137,z1,z2,z3,z5,z8,z450]),(0,[z1,z2,z3,z5,z41,z20,z6]),(0,[z1,z526,z2,z3,z5,z8,z6]),(0,[z116,z1,z2,z100,z3,z5,z6]),(0,[z1,z2,z3,z5,z20,z6,z27])],[(0,[z527,z1,z2,z3,z5,z8,z6]),(0,[z528,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z529,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z149,z21,z6])],[(0,[z28,z1,z2,z3,z92,z8,z6]),(0,[z17,z1,z231,z2,z3,z5,z6]),(0,[z1,z25,z2,z3,z106,z5,z8]),(0,[z299,z1,z2,z3,z33,z5,z6])],[(0,[z1,z2,z3,z4,z8,z20,z6]),(0,[z1,z2,z57,z3,z5,z89,z6]),(0,[z1,z11,z2,z3,z5,z8,z6]),(0,[z1,z11,z2,z3,z5,z149,z6])],[(0,[z1,z2,z3,z530,z5,z8,z6]),(0,[z1,z44,z2,z3,z106,z5,z8]),(0,[z1,z2,z57,z3,z5,z72,z6]),(1,[z1,z2,z3,z42,z6,z27])],[(1,[z1,z2,z3,z5,z500,z6]),(1,[z1,z2,z385,z3,z5,z6]),(0,[z1,z2,z3,z4,z33,z5,z6]),(0,[z1,z2,z26,z3,z5,z41,z6])],[(0,[z1,z204,z3,z38,z5,z8,z6]),(0,[z1,z11,z2,z3,z5,z6,z187]),(0,[z1,z2,z57,z3,z5,z6,z70])],[(0,[z137,z1,z2,z3,z5,z500,z6]),(0,[z131,z1,z2,z57,z3,z5,z6]),(1,[z1,z218,z2,z3,z5,z6]),(0,[z1,z2,z207,z3,z5,z8,z6]),(0,[z1,z531,z2,z3,z5,z8,z6])],[(0,[z43,z1,z2,z3,z42,z8,z6]),(0,[z17,z1,z2,z3,z60,z5,z6]),(0,[z1,z2,z3,z227,z5,z8,z6])],[(1,[z1,z2,z3,z5,z169,z6]),(0,[z1,z2,z3,z5,z8,z6,z532])],[(0,[z1,z533,z2,z3,z5,z8,z6]),(0,[z1,z11,z2,z3,z5,z115,z6]),(0,[z17,z1,z2,z3,z106,z5,z6]),(1,[z1,z374,z2,z3,z5,z6])],[(0,[z534,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z535,z6]),(0,[z1,z2,z3,z5,z88,z8,z6]),(0,[z1,z2,z3,z5,z72,z6,z27])],[(1,[z17,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z103,z6])],[(0,[z28,z1,z2,z3,z5,z41,z6]),(1,[z1,z2,z3,z5,z6,z27])],[(0,[z15,z16,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z94,z6]),(0,[z1,z2,z3,z101,z5,z21,z6]),(0,[z1,z2,z3,z5,z8,z367,z6])],[(0,[z116,z28,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z98,z5,z8,z6]),(0,[z131,z1,z2,z3,z5,z21,z6]),(0,[z1,z56,z2,z3,z5,z6,z27]),(0,[z17,z116,z1,z2,z3,z5,z6])]],
   [[],[(0,[z1,z2,z385,z139,z3,z5,z6]),(1,[z1,z2,z3,z5,z444,z6]),(0,[z1,z2,z3,z536,z5,z8,z6]),(0,[z43,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z6,z480]),(0,[z1,z2,z3,z8,z20,z537,z6])],[(0,[z1,z2,z3,z5,z8,z6,z538]),(0,[z1,z2,z3,z5,z41,z198,z6]),(0,[z1,z2,z3,z60,z8,z20,z6]),(0,[z17,z1,z2,z3,z5,z97,z6]),(0,[z1,z2,z57,z3,z5,z20,z6]),(0,[z539,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z6,z27,z297])],[(0,[z1,z2,z3,z92,z89,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z228]),(0,[z1,z2,z3,z8,z20,z6,z84]),(0,[z540,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z57,z3,z5,z88,z6])],[(0,[z1,z2,z3,z60,z33,z5,z6]),(0,[z541,z1,z2,z3,z5,z8,z6])],[(0,[z43,z1,z2,z60,z5,z8,z6]),(1,[z1,z2,z3,z42,z5,z27]),(0,[z1,z2,z3,z33,z33,z5,z6])],[(0,[z542,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z8,z6,z70])],[(0,[z543,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z118,z5,z8,z6]),(0,[z1,z2,z51,z3,z5,z6,z27]),(0,[z1,z2,z3,z488,z5,z8,z6]),(0,[z1,z2,z342,z3,z8,z20,z6])],[(0,[z1,z544,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z545,z5,z8,z6]),(0,[z17,z1,z2,z3,z5,z89,z6]),(0,[z1,z2,z3,z5,z8,z546,z6]),(0,[z1,z2,z3,z547,z42,z8,z6])],[(0,[z1,z2,z3,z106,z5,z21,z6]),(0,[z148,z2,z3,z5,z41,z8,z6]),(0,[z148,z1,z2,z3,z42,z8,z6]),(0,[z17,z1,z2,z3,z5,z72,z6]),(0,[z1,z2,z3,z8,z20,z6,z6])],[(0,[z1,z2,z548,z3,z5,z8,z6]),(0,[z1,z2,z48,z3,z5,z6,z27])],[(0,[z1,z2,z3,z5,z549,z8,z6]),(1,[z1,z11,z2,z3,z42,z6]),(0,[z17,z1,z2,z3,z5,z6,z70])],[(0,[z1,z2,z3,z215,z5,z8,z6]),(0,[z1,z2,z3,z498,z5,z6,z27])],[(0,[z1,z2,z3,z550,z5,z8,z6])],[(1,[z1,z2,z3,z314,z8,z6]),(0,[z36,z1,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z551,z8,z6]),(0,[z1,z2,z3,z5,z8,z246,z6]),(0,[z172,z1,z2,z3,z5,z8,z6]),(0,[z116,z1,z2,z5,z88,z8,z6])]],
   [[(0,[z107,z1,z2,z3,z5,z6,z27]),(0,[z1,z1,z2,z3,z5,z41,z6]),(0,[z43,z1,z2,z3,z65,z8,z6]),(0,[z116,z1,z2,z3,z53,z5,z6]),(0,[z1,z2,z3,z42,z308,z8,z6]),(0,[z1,z2,z3,z5,z18,z6,z27])],[(0,[z151,z1,z2,z3,z33,z5,z6]),(1,[z1,z2,z3,z503,z5,z6]),(1,[z1,z2,z57,z3,z20,z6]),(0,[z1,z552,z2,z3,z5,z8,z6])],[(0,[z553,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z554,z5,z8,z6]),(0,[z1,z555,z2,z3,z5,z8,z6]),(0,[z1,z2,z556,z3,z5,z8,z6]),(0,[z1,z2,z3,z547,z5,z8,z6]),(1,[z1,z2,z3,z5,z6,z557]),(0,[z1,z2,z3,z5,z6,z77,z27])],[],[(0,[z137,z1,z2,z3,z5,z501,z6]),(0,[z1,z2,z57,z3,z5,z198,z6]),(0,[z1,z2,z3,z5,z558,z8,z6]),(0,[z116,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z42,z33,z5,z6]),(0,[z1,z2,z3,z8,z20,z559,z6])],[(0,[z17,z1,z44,z2,z3,z5,z6]),(1,[z1,z2,z3,z33,z91,z6])],[(0,[z1,z16,z2,z3,z8,z20,z6])],[(0,[z36,z1,z329,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z330,z41,z6])],[(0,[z1,z2,z560,z3,z5,z8,z6]),(0,[z17,z1,z2,z3,z5,z20,z6]),(0,[z17,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z193,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z27])],[(0,[z1,z2,z3,z5,z501,z8,z6]),(0,[z24,z43,z1,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z5,z88,z6]),(0,[z1,z2,z3,z227,z101,z5,z6]),(0,[z561,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z33,z5,z41,z6]),(0,[z562,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z287,z8,z6]),(0,[z1,z2,z3,z521,z5,z8,z6]),(0,[z9,z1,z2,z3,z5,z6,z27]),(1,[z1,z2,z3,z362,z5,z6])],[(0,[z1,z2,z3,z5,z8,z84,z69]),(0,[z1,z2,z3,z5,z563,z8,z6]),(0,[z1,z2,z3,z564,z5,z8,z6]),(1,[z1,z2,z3,z42,z8,z27]),(0,[z1,z2,z3,z565,z5,z8,z6])],[],[(0,[z1,z2,z3,z42,z92,z8,z6]),(0,[z1,z2,z3,z87,z5,z41,z6])],[(0,[z1,z2,z3,z5,z21,z115,z6]),(0,[z1,z2,z566,z3,z5,z8,z6]),(0,[z1,z2,z3,z300,z5,z8,z6]),(0,[z567,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z568,z3,z5,z8,z6]),(0,[z1,z2,z376,z3,z33,z5,z6]),(0,[z1,z2,z3,z375,z33,z5,z6])]],
   [[(1,[z1,z2,z3,z5,z377,z6]),(0,[z1,z2,z3,z569,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z570,z6])],[(0,[z110,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z272,z6]),(0,[z1,z2,z57,z51,z3,z5,z6]),(0,[z1,z2,z26,z3,z8,z20,z6])],[(0,[z170,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z33,z5,z91,z6])],[(0,[z1,z178,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z571,z6]),(0,[z1,z2,z100,z3,z5,z6,z27]),(0,[z1,z2,z26,z3,z33,z5,z6])],[(0,[z15,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z38,z8,z20,z6]),(1,[z1,z2,z3,z5,z103,z6])],[(0,[z1,z2,z3,z418,z5,z8,z6]),(0,[z257,z1,z11,z2,z3,z5,z6])],[(0,[z151,z1,z2,z3,z5,z41,z6]),(1,[z1,z2,z3,z5,z563,z6]),(0,[z1,z572,z2,z3,z5,z8,z6])],[(0,[z1,z177,z2,z57,z3,z5,z6]),(0,[z1,z2,z3,z42,z53,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z339])],[(0,[z1,z2,z3,z573,z5,z8,z6]),(0,[z219,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z574,z8,z6]),(0,[z1,z2,z3,z33,z106,z5,z6])],[(0,[z575,z1,z2,z3,z5,z8,z6]),(0,[z576,z1,z2,z3,z5,z8,z6]),(0,[z28,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z5,z92,z21,z6]),(0,[z1,z2,z3,z42,z5,z41,z6]),(0,[z116,z1,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z42,z149,z8,z6])],[(0,[z1,z2,z139,z3,z5,z6,z27]),(0,[z1,z2,z266,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z158,z6]),(0,[z17,z1,z2,z3,z5,z198,z6]),(0,[z1,z25,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z5,z97,z6,z260]),(0,[z1,z577,z2,z3,z5,z8,z6])],[(0,[z129,z1,z2,z3,z5,z8,z10]),(1,[z1,z2,z3,z5,z6,z505]),(0,[z1,z2,z3,z578,z5,z8,z6]),(0,[z1,z2,z3,z42,z33,z8,z6])],[(0,[z1,z139,z3,z60,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z10,z6]),(0,[z1,z2,z3,z554,z38,z5,z6]),(0,[z1,z11,z2,z48,z3,z5,z6]),(0,[z142,z17,z1,z2,z3,z5,z6]),(0,[z1,z44,z2,z3,z5,z6,z27])],[(1,[z137,z139,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z115,z6,z27]),(0,[z1,z2,z3,z5,z8,z6,z557])],[(0,[z1,z2,z49,z3,z42,z8,z6]),(0,[z17,z1,z204,z2,z3,z5,z6]),(0,[z58,z17,z1,z2,z3,z5,z6])],[(0,[z257,z1,z2,z3,z5,z21,z6]),(0,[z1,z177,z2,z3,z5,z21,z6]),(1,[z1,z2,z3,z343,z5,z8]),(0,[z1,z2,z3,z8,z20,z6,z69]),(0,[z1,z2,z48,z3,z5,z8,z72]),(0,[z1,z2,z3,z5,z8,z6,z579]),(0,[z58,z1,z2,z3,z5,z6,z27])]],
   [[(0,[z1,z2,z3,z38,z92,z8,z6]),(0,[z1,z2,z3,z5,z122,z8,z6]),(0,[z1,z2,z3,z5,z8,z580,z6]),(0,[z1,z2,z51,z3,z5,z563,z6]),(0,[z1,z2,z3,z33,z5,z97,z6])],[],[(0,[z1,z2,z3,z93,z5,z8,z6]),(1,[z1,z2,z3,z5,z6,z581])],[(0,[z1,z2,z3,z5,z8,z19,z6]),(0,[z1,z2,z3,z582,z5,z8,z6])],[(0,[z466,z1,z2,z3,z5,z40,z6])],[(0,[z1,z177,z139,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z203,z8,z6]),(0,[z116,z1,z2,z3,z60,z5,z6]),(0,[z1,z2,z3,z583,z5,z8,z6]),(0,[z1,z2,z3,z584,z5,z8,z6]),(0,[z17,z1,z2,z2,z3,z5,z6]),(0,[z585,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z253,z5,z8,z6]),(0,[z1,z2,z3,z8,z20,z6,z187])],[(0,[z116,z1,z2,z139,z3,z5,z6]),(1,[z1,z2,z3,z5,z8,z206]),(0,[z17,z131,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z468,z8,z6]),(0,[z17,z1,z3,z5,z149,z8,z6])],[(0,[z1,z2,z49,z3,z5,z8,z6]),(0,[z1,z2,z3,z586,z5,z8,z6]),(0,[z1,z2,z3,z5,z21,z161,z6]),(1,[z1,z2,z3,z5,z246,z6]),(0,[z17,z1,z2,z51,z3,z5,z6]),(0,[z1,z2,z3,z33,z5,z89,z6]),(0,[z116,z1,z2,z3,z106,z5,z6])],[(0,[z131,z1,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z33,z5,z72,z6]),(0,[z1,z2,z3,z5,z8,z34,z6])],[(0,[z587,z1,z2,z3,z5,z8,z6]),(0,[z110,z1,z2,z3,z5,z8,z6]),(0,[z36,z1,z2,z3,z33,z5,z6]),(1,[z1,z2,z3,z5,z29,z6])],[(0,[z1,z2,z3,z33,z5,z6,z70])],[(0,[z1,z2,z49,z60,z5,z8,z6]),(0,[z1,z2,z3,z38,z5,z41,z6]),(1,[z1,z2,z3,z59,z34,z6]),(0,[z1,z2,z3,z59,z5,z6,z27])],[(0,[z1,z2,z588,z3,z5,z8,z6]),(0,[z589,z1,z2,z3,z5,z8,z6]),(0,[z116,z116,z1,z2,z3,z5,z6]),(0,[z590,z1,z2,z3,z42,z8,z6])],[(0,[z591,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z34,z6,z27])],[(0,[z1,z2,z3,z592,z5,z8,z6]),(0,[z1,z2,z3,z593,z5,z8,z6])],[(0,[z1,z11,z2,z196,z3,z5,z6]),(0,[z116,z1,z2,z3,z5,z97,z6]),(0,[z1,z2,z3,z42,z8,z97,z6]),(0,[z1,z2,z3,z594,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z281,z5,z8,z6]),(0,[z1,z595,z2,z3,z5,z8,z6]),(0,[z1,z2,z596,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z597,z6])],[(0,[z137,z17,z1,z2,z3,z5,z6]),(0,[z1,z11,z2,z57,z3,z5,z6]),(0,[z1,z2,z3,z276,z5,z8,z6]),(0,[z420,z1,z2,z3,z8,z20,z6])],[(0,[z137,z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z5,z40,z21,z6]),(0,[z129,z1,z2,z3,z42,z8,z6]),(0,[z9,z1,z2,z3,z5,z73,z6]),(0,[z1,z2,z3,z359,z33,z5,z6]),(1,[z1,z2,z3,z462,z33,z6])],[(0,[z1,z2,z598,z3,z5,z8,z6])],[(0,[z129,z1,z2,z3,z5,z8,z84])],[(0,[z1,z2,z3,z5,z8,z158,z6]),(0,[z131,z1,z2,z3,z5,z8,z195]),(0,[z1,z2,z3,z53,z5,z21,z6]),(0,[z1,z2,z3,z5,z8,z599,z6])],[(0,[z1,z2,z3,z5,z8,z6,z505]),(0,[z142,z43,z1,z2,z3,z5,z6]),(0,[z116,z1,z2,z3,z5,z89,z6]),(1,[z1,z2,z3,z289,z8,z6]),(0,[z1,z2,z3,z33,z8,z20,z6]),(0,[z1,z2,z3,z33,z5,z20,z6])],[(0,[z1,z11,z2,z212,z3,z5,z6]),(0,[z1,z3,z5,z149,z8,z198,z6]),(0,[z116,z1,z2,z3,z5,z72,z6]),(0,[z1,z2,z3,z33,z5,z88,z6]),(0,[z1,z2,z3,z42,z8,z72,z6]),(0,[z600,z1,z2,z3,z42,z8,z6])],[(0,[z340,z1,z2,z3,z8,z20,z6])],[(1,[z1,z2,z3,z5,z287,z6]),(0,[z1,z11,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z38,z40,z8,z6]),(0,[z116,z1,z2,z3,z5,z6,z70])],[(0,[z1,z2,z3,z5,z89,z6,z27]),(0,[z1,z2,z3,z5,z436,z8,z6]),(0,[z1,z2,z57,z3,z242,z5,z6]),(0,[z1,z2,z26,z3,z5,z430,z6]),(0,[z1,z2,z601,z3,z5,z8,z6]),(0,[z1,z2,z3,z87,z8,z20,z6])],[(0,[z1,z2,z3,z147,z5,z8,z6]),(0,[z129,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z602,z5,z8,z6])],[(0,[z1,z2,z3,z603,z5,z8,z6]),(0,[z1,z2,z604,z3,z5,z8,z6]),(0,[z1,z2,z3,z87,z33,z5,z6])],[(0,[z151,z2,z49,z3,z5,z8,z6]),(0,[z1,z605,z2,z3,z5,z8,z6]),(0,[z1,z2,z207,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z8,z6,z581]),(0,[z1,z2,z3,z8,z464,z6,z84]),(0,[z1,z2,z3,z5,z606,z8,z6])],[(0,[z36,z1,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z42,z106,z8,z6])],[(0,[z1,z2,z607,z3,z5,z8,z6]),(0,[z43,z1,z2,z57,z3,z5,z6]),(0,[z58,z1,z2,z3,z5,z34,z6]),(0,[z257,z1,z2,z3,z33,z5,z6])]],
   [[(0,[z1,z608,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z361,z6]),(0,[z1,z2,z3,z609,z5,z8,z6])],[(0,[z137,z2,z139,z3,z5,z8,z6]),(0,[z610,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z611,z6]),(0,[z1,z2,z3,z5,z88,z21,z6]),(0,[z1,z2,z3,z5,z8,z10,z69]),(0,[z612,z1,z2,z3,z5,z8,z6]),(0,[z540,z1,z2,z57,z3,z5,z6]),(1,[z1,z2,z3,z488,z5,z6]),(0,[z1,z2,z613,z3,z5,z8,z6])],[(0,[z1,z2,z3,z614,z5,z8,z6]),(0,[z615,z1,z2,z3,z5,z8,z6]),(0,[z151,z1,z2,z3,z8,z20,z6]),(0,[z1,z177,z2,z3,z5,z277,z6]),(0,[z616,z1,z2,z3,z5,z8,z6]),(1,[z1,z11,z2,z3,z20,z6]),(0,[z116,z1,z44,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z617,z6]),(0,[z116,z1,z2,z3,z5,z6,z411])],[(0,[z1,z2,z57,z3,z5,z6,z27]),(0,[z1,z2,z3,z53,z5,z8,z237])],[(0,[z137,z1,z2,z3,z314,z8,z6]),(0,[z1,z618,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z619,z6]),(0,[z1,z2,z57,z3,z5,z467,z6])],[(0,[z116,z1,z2,z3,z5,z20,z6]),(0,[z116,z1,z2,z3,z8,z20,z6]),(0,[z620,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z8,z20,z6]),(0,[z1,z2,z3,z33,z5,z8,z18])],[(0,[z1,z2,z3,z5,z8,z621,z6]),(0,[z1,z622,z2,z3,z5,z8,z6]),(0,[z148,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z423,z6]),(0,[z116,z1,z2,z3,z5,z88,z6]),(1,[z1,z2,z3,z8,z482,z6])],[(0,[z43,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z359,z5,z41,z6]),(0,[z1,z204,z2,z3,z5,z6,z27]),(0,[z1,z2,z623,z3,z5,z8,z6]),(0,[z1,z2,z3,z624,z5,z8,z6]),(1,[z1,z2,z3,z5,z337,z6])],[(0,[z1,z2,z625,z3,z5,z8,z6]),(0,[z1,z2,z3,z33,z5,z198,z6]),(0,[z452,z1,z2,z3,z33,z5,z6])],[(1,[z1,z266,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z626,z6]),(0,[z1,z2,z627,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z537,z6]),(0,[z1,z2,z3,z87,z5,z8,z18])],[(0,[z1,z2,z71,z3,z5,z6,z27]),(0,[z1,z2,z3,z5,z8,z628,z6])],[(0,[z1,z2,z3,z5,z8,z6,z84]),(0,[z1,z629,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z59,z5,z34,z6]),(0,[z1,z2,z3,z59,z8,z34,z6])],[(0,[z1,z2,z3,z630,z5,z8,z6])],[(0,[z1,z2,z3,z631,z5,z8,z6]),(0,[z1,z632,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z21,z230,z6]),(0,[z1,z2,z3,z633,z5,z8,z6]),(0,[z365,z1,z2,z3,z5,z8,z6])],[(0,[z1,z329,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z92,z41,z6]),(1,[z116,z1,z2,z3,z42,z6])],[(0,[z1,z2,z3,z634,z5,z8,z6]),(1,[z1,z2,z3,z42,z8,z84]),(0,[z17,z9,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z6,z635]),(0,[z1,z2,z3,z636,z5,z8,z6])]],
   [[(0,[z1,z2,z556,z57,z3,z5,z6])],[(0,[z36,z116,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z21,z236,z6]),(0,[z1,z11,z2,z3,z637,z5,z6]),(0,[z219,z1,z2,z48,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z18,z6])],[(0,[z151,z1,z2,z3,z5,z479,z6]),(0,[z131,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z5,z8,z6,z6]),(0,[z1,z2,z3,z5,z8,z6,z638]),(0,[z1,z639,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z6,z557,z27]),(0,[z1,z2,z3,z462,z33,z5,z6])],[(0,[z107,z2,z3,z5,z8,z21,z6]),(0,[z640,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z93,z89,z8,z6]),(0,[z257,z1,z2,z3,z5,z41,z6]),(0,[z1,z177,z2,z3,z5,z41,z6]),(0,[z124,z17,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z5,z8,z18])],[(0,[z36,z151,z2,z3,z5,z8,z6]),(0,[z1,z2,z641,z3,z5,z8,z6]),(0,[z1,z11,z2,z3,z53,z5,z6]),(1,[z1,z2,z3,z42,z33,z6])],[(0,[z1,z2,z3,z8,z198,z20,z6]),(0,[z1,z2,z642,z3,z5,z8,z6]),(1,[z1,z2,z3,z42,z8,z6])],[(0,[z1,z177,z16,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z73,z6]),(0,[z1,z2,z3,z637,z5,z8,z6]),(0,[z116,z1,z2,z3,z5,z198,z6]),(0,[z1,z2,z3,z42,z8,z198,z6]),(0,[z1,z2,z57,z3,z503,z5,z6])],[(0,[z443,z1,z2,z3,z5,z41,z6]),(0,[z1,z56,z2,z3,z42,z8,z6]),(0,[z17,z17,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z8,z643,z6]),(0,[z1,z2,z3,z5,z149,z41,z6]),(0,[z1,z2,z3,z5,z644,z8,z6]),(0,[z465,z1,z2,z3,z33,z5,z6])],[],[(0,[z116,z1,z204,z2,z3,z5,z6]),(0,[z1,z2,z3,z106,z8,z20,z6])],[(0,[z1,z2,z3,z5,z8,z559,z6])],[(0,[z1,z2,z3,z5,z6,z27,z456])],[(0,[z1,z2,z51,z4,z5,z8,z6]),(0,[z1,z2,z3,z5,z21,z21,z6]),(0,[z1,z2,z3,z5,z8,z645,z6])],[]],
   [[(0,[z1,z2,z3,z5,z8,z6,z646]),(0,[z1,z218,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z647,z5,z8,z6]),(0,[z1,z2,z51,z3,z42,z8,z6]),(0,[z17,z1,z2,z3,z427,z5,z6])],[(0,[z211,z1,z2,z3,z60,z5,z6]),(0,[z1,z56,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z362,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z482,z6])],[(0,[z15,z1,z2,z57,z3,z5,z6]),(0,[z1,z191,z25,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z337,z6])],[(0,[z116,z131,z1,z2,z3,z5,z6]),(0,[z1,z2,z57,z3,z5,z34,z6]),(1,[z1,z2,z3,z120,z5,z6])],[(0,[z36,z1,z2,z3,z5,z461,z6]),(0,[z116,z1,z2,z51,z3,z5,z6]),(0,[z1,z2,z48,z3,z42,z8,z6]),(1,[z1,z2,z3,z33,z5,z18])],[(0,[z648,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z101,z5,z41,z6]),(0,[z1,z2,z3,z5,z41,z6,z581]),(0,[z1,z2,z3,z5,z8,z6,z649]),(1,[z1,z2,z3,z42,z8,z20])],[(0,[z131,z1,z2,z3,z5,z41,z6]),(1,[z1,z2,z3,z8,z419,z6]),(0,[z257,z116,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z8,z6,z650]),(0,[z278,z1,z2,z3,z5,z6,z27])],[(0,[z107,z1,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z5,z8,z651,z6]),(0,[z441,z116,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z462,z33,z8,z6])],[(0,[z15,z1,z2,z3,z5,z21,z6]),(0,[z36,z1,z2,z3,z8,z20,z6]),(0,[z652,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z40,z8,z6]),(0,[z1,z2,z3,z106,z5,z8,z18])],[(0,[z491,z1,z2,z3,z5,z8,z6]),(0,[z1,z11,z2,z3,z550,z5,z6]),(1,[z1,z497,z2,z3,z5,z6])],[(1,[z1,z2,z3,z33,z20,z6])],[(0,[z1,z2,z3,z5,z8,z653,z6]),(0,[z1,z2,z3,z332,z5,z8,z6]),(0,[z1,z2,z3,z5,z6,z84,z228]),(0,[z448,z116,z1,z2,z3,z5,z6]),(0,[z1,z2,z48,z3,z5,z8,z6]),(0,[z1,z2,z26,z3,z106,z5,z8])],[(0,[z1,z11,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z654,z8,z6]),(1,[z1,z2,z3,z5,z294,z6])],[(0,[z1,z2,z3,z5,z8,z6,z655]),(0,[z1,z11,z177,z2,z3,z5,z6]),(0,[z1,z497,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z498,z5,z8,z6])]],
   [[(0,[z15,z1,z139,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z37,z6])],[(0,[z1,z2,z47,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z656,z6])],[(0,[z107,z1,z2,z3,z5,z8,z6]),(1,[z107,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z106,z5,z41,z6]),(0,[z1,z2,z3,z657,z5,z8,z6]),(0,[z1,z11,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z658,z8,z6])],[(0,[z1,z2,z2,z3,z5,z8,z6]),(0,[z659,z1,z2,z3,z5,z8,z6])],[(0,[z372,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z6,z27]),(0,[z9,z1,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z5,z8,z660,z6]),(0,[z1,z2,z3,z5,z321,z8,z6]),(0,[z1,z2,z3,z661,z5,z8,z6]),(1,[z1,z2,z3,z251,z5,z6])],[(0,[z1,z2,z3,z5,z662,z8,z6]),(0,[z1,z2,z3,z5,z344,z6,z70]),(0,[z1,z2,z3,z5,z656,z6,z69])],[(0,[z663,z1,z2,z3,z5,z8,z6]),(0,[z9,z1,z2,z3,z5,z8,z84]),(0,[z664,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z462,z8,z6])],[(0,[z1,z2,z3,z4,z5,z6,z27]),(0,[z131,z1,z2,z3,z5,z334,z6]),(0,[z1,z2,z3,z5,z8,z6,z69]),(0,[z1,z665,z2,z3,z5,z8,z6])],[(0,[z1,z2,z57,z3,z5,z92,z6]),(0,[z1,z11,z2,z100,z3,z5,z6]),(0,[z590,z1,z2,z3,z5,z8,z6])],[(0,[z140,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z42,z8,z10]),(1,[z142,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z130,z6]),(0,[z17,z1,z2,z3,z5,z34,z6]),(0,[z1,z2,z3,z42,z88,z8,z6])],[(0,[z1,z2,z3,z5,z8,z8,z6]),(0,[z1,z2,z3,z5,z41,z18,z6]),(0,[z129,z9,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z666,z5,z8,z6]),(0,[z1,z2,z3,z42,z8,z103,z6])],[(0,[z1,z11,z2,z139,z3,z5,z6]),(0,[z1,z2,z57,z3,z4,z5,z6]),(0,[z1,z2,z212,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z45,z6])],[(0,[z1,z2,z3,z5,z8,z667,z6]),(0,[z1,z2,z100,z3,z42,z8,z6]),(0,[z197,z1,z2,z3,z5,z6,z27])],[(0,[z1,z2,z49,z3,z5,z21,z6]),(0,[z9,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z187]),(0,[z1,z2,z3,z5,z668,z8,z6])],[],[]],
   [[(0,[z1,z2,z3,z5,z8,z6,z669]),(0,[z43,z1,z11,z2,z3,z5,z6]),(0,[z1,z177,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z5,z8,z6,z670]),(0,[z257,z1,z2,z3,z8,z20,z6]),(0,[z1,z2,z3,z356,z5,z8,z6])],[(0,[z1,z2,z3,z79,z4,z5,z6]),(0,[z1,z2,z3,z5,z169,z8,z6]),(1,[z1,z2,z3,z418,z5,z8]),(1,[z1,z2,z3,z42,z8,z187])],[(0,[z1,z2,z3,z5,z156,z8,z6]),(0,[z1,z2,z3,z5,z6,z84,z27]),(0,[z1,z2,z3,z671,z5,z8,z6]),(0,[z1,z177,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z5,z8,z419,z6]),(1,[z1,z2,z3,z498,z8,z6])],[(0,[z1,z2,z139,z3,z42,z8,z6]),(0,[z600,z1,z2,z3,z5,z8,z6]),(0,[z1,z25,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z5,z8,z672,z6]),(0,[z1,z442,z2,z3,z8,z20,z6])],[(0,[z1,z2,z48,z3,z42,z5,z8])],[(0,[z1,z2,z3,z673,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z674,z6]),(0,[z1,z2,z3,z5,z675,z8,z6]),(0,[z1,z44,z2,z3,z42,z8,z6]),(0,[z1,z2,z57,z3,z5,z40,z6]),(0,[z1,z2,z57,z5,z8,z115,z6])],[(0,[z1,z2,z3,z5,z8,z676,z6]),(0,[z1,z2,z3,z60,z5,z6,z27]),(0,[z1,z2,z3,z677,z5,z8,z6]),(0,[z17,z1,z11,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z380,z6]),(0,[z1,z2,z217,z3,z5,z6,z27])],[(0,[z1,z678,z2,z3,z5,z8,z6]),(0,[z437,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z341,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z41,z10,z6]),(0,[z1,z191,z2,z3,z5,z8,z6]),(0,[z58,z1,z2,z3,z42,z8,z6])],[(0,[z129,z1,z2,z57,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z294,z6]),(0,[z1,z2,z679,z3,z5,z8,z6])],[(1,[z1,z2,z138,z5,z8,z6]),(0,[z1,z2,z3,z5,z680,z8,z6]),(0,[z382,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z604,z57,z3,z5,z6]),(1,[z219,z1,z2,z3,z5,z6]),(0,[z1,z681,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z682,z8,z6]),(0,[z1,z2,z3,z5,z8,z683,z6])],[(0,[z1,z516,z2,z3,z8,z20,z6])],[(0,[z684,z1,z2,z3,z5,z8,z6]),(0,[z116,z9,z1,z2,z3,z5,z6]),(0,[z17,z1,z56,z2,z3,z5,z6]),(0,[z1,z2,z57,z3,z5,z18,z6]),(0,[z1,z2,z3,z5,z8,z656,z6])],[(0,[z685,z1,z2,z3,z5,z8,z6]),(0,[z350,z17,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z686,z8,z6]),(0,[z17,z1,z2,z3,z5,z92,z6]),(0,[z1,z11,z2,z3,z5,z6,z70]),(0,[z1,z44,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z8,z21,z20,z6]),(1,[z1,z2,z3,z554,z5,z6]),(0,[z687,z1,z2,z3,z5,z8,z6])]],
   [[(0,[z17,z1,z2,z3,z5,z327,z6])],[(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z688,z8,z6]),(0,[z129,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z8,z6,z689]),(0,[z553,z1,z11,z2,z3,z5,z6]),(0,[z1,z555,z11,z2,z3,z5,z6]),(0,[z58,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z184,z5,z8,z6]),(0,[z1,z2,z3,z143,z5,z8,z6]),(0,[z1,z56,z2,z3,z38,z8,z6]),(0,[z1,z2,z3,z5,z423,z8,z6]),(0,[z1,z2,z3,z101,z8,z20,z6]),(0,[z1,z2,z48,z3,z5,z8,z69]),(0,[z164,z1,z2,z3,z42,z8,z6]),(0,[z1,z183,z2,z3,z5,z8,z6])],[(0,[z690,z1,z2,z3,z5,z8,z6]),(0,[z131,z1,z2,z3,z8,z20,z6]),(1,[z443,z1,z2,z3,z5,z6]),(0,[z1,z2,z691,z3,z5,z8,z6]),(0,[z1,z56,z2,z3,z89,z8,z6]),(0,[z116,z1,z2,z176,z3,z5,z6]),(0,[z116,z1,z374,z2,z3,z5,z6]),(0,[z1,z66,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z692])],[(0,[z148,z1,z2,z57,z3,z5,z6]),(0,[z1,z2,z3,z5,z41,z34,z6]),(0,[z1,z2,z3,z693,z5,z8,z6]),(1,[z116,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z5,z8,z6,z694])],[],[(0,[z1,z2,z3,z5,z8,z45,z6]),(1,[z1,z2,z3,z8,z67,z6]),(0,[z1,z2,z3,z53,z8,z20,z6]),(0,[z1,z2,z3,z42,z8,z6,z27])],[(1,[z1,z2,z3,z254,z8,z6]),(0,[z466,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z695,z3,z5,z8,z6]),(0,[z1,z2,z3,z53,z33,z5,z6])],[(1,[z1,z2,z3,z5,z6,z74]),(1,[z1,z2,z3,z432,z5,z8])],[(0,[z696,z1,z2,z3,z5,z8,z6]),(0,[z1,z16,z2,z3,z5,z6,z27]),(0,[z1,z2,z57,z3,z5,z10,z6]),(1,[z1,z2,z3,z5,z78,z6]),(0,[z1,z11,z2,z3,z8,z20,z6]),(0,[z1,z2,z26,z5,z8,z6,z69])],[(0,[z137,z1,z2,z3,z42,z8,z6]),(0,[z1,z2,z697,z3,z5,z8,z6]),(0,[z17,z1,z2,z3,z5,z40,z6]),(1,[z1,z44,z2,z3,z42,z8]),(0,[z1,z2,z3,z5,z698,z8,z6])],[(1,[z131,z2,z3,z93,z8,z6]),(0,[z148,z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z699,z8,z6]),(0,[z1,z11,z2,z3,z33,z5,z6]),(0,[z17,z1,z2,z3,z5,z6,z27])],[(0,[z1,z2,z700,z3,z5,z8,z6]),(0,[z1,z2,z3,z701,z5,z8,z6]),(0,[z1,z2,z3,z5,z702,z8,z6])],[(0,[z1,z2,z3,z101,z92,z8,z6]),(0,[z1,z2,z703,z3,z5,z8,z6])],[(0,[z15,z1,z2,z3,z5,z41,z6]),(0,[z131,z1,z2,z3,z92,z8,z6]),(0,[z704,z1,z2,z3,z5,z8,z6]),(0,[z705,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z706,z3,z5,z8,z6]),(1,[z1,z2,z3,z91,z8,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z5,z8,z707]),(0,[z1,z2,z3,z92,z8,z80]),(0,[z1,z2,z3,z5,z8,z708]),(0,[z709,z1,z2,z3,z5,z6]),(0,[z1,z25,z3,z5,z97,z27]),(0,[z1,z2,z47,z3,z5,z413])],[(0,[z137,z139,z3,z314,z8,z6]),(0,[z2,z3,z5,z41,z710,z6]),(0,[z9,z2,z3,z33,z5,z10]),(0,[z1,z2,z3,z5,z711,z6])],[(0,[z17,z1,z2,z138,z5,z6]),(0,[z712,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z281,z713,z6]),(0,[z1,z11,z2,z100,z101,z6])],[(0,[z443,z1,z3,z5,z149,z6]),(0,[z714,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z592,z8]),(0,[z1,z2,z48,z57,z3,z42]),(0,[z1,z66,z2,z3,z42,z6])],[(0,[z1,z2,z3,z5,z715,z6]),(0,[z36,z2,z4,z5,z21,z6]),(0,[z492,z2,z3,z5,z21,z6]),(0,[z1,z2,z716,z3,z5,z6]),(0,[z116,z1,z2,z217,z5,z6]),(0,[z58,z1,z2,z3,z482,z6])],[(0,[z43,z1,z60,z5,z41,z6]),(0,[z1,z2,z3,z717,z5,z6]),(0,[z1,z2,z26,z3,z42,z41]),(0,[z211,z1,z2,z3,z42,z6]),(0,[z1,z2,z3,z42,z8,z291])],[(0,[z1,z2,z47,z48,z3,z42])],[(0,[z382,z1,z2,z57,z5,z6]),(0,[z1,z267,z2,z3,z42,z8]),(0,[z116,z1,z2,z3,z718,z6]),(0,[z116,z1,z2,z26,z5,z69])],[(0,[z1,z2,z3,z5,z719,z6]),(0,[z1,z2,z3,z5,z720,z6]),(0,[z1,z349,z2,z3,z321,z6]),(0,[z1,z2,z3,z5,z6,z721]),(0,[z1,z2,z3,z289,z6,z27]),(0,[z219,z1,z722,z3,z5,z6]),(0,[z1,z531,z2,z3,z42,z8])],[(0,[z1,z2,z35,z5,z501,z6]),(0,[z1,z2,z3,z41,z20,z6]),(0,[z1,z2,z3,z5,z723,z6]),(0,[z1,z2,z3,z20,z6,z27])],[(0,[z1,z2,z138,z5,z8,z450]),(0,[z1,z2,z3,z5,z724,z6]),(0,[z1,z2,z3,z5,z710,z6]),(0,[z1,z2,z3,z725,z8,z6])],[(0,[z1,z2,z138,z8,z20,z6]),(0,[z1,z2,z207,z5,z115,z6]),(0,[z1,z2,z3,z726,z8,z6])],[(0,[z1,z2,z3,z5,z727,z6]),(0,[z17,z1,z25,z3,z5,z97]),(0,[z1,z2,z71,z57,z40,z6]),(1,[z1,z497,z2,z3,z42])],[(0,[z1,z2,z3,z728,z8,z6]),(0,[z1,z2,z3,z464,z6,z729]),(0,[z116,z1,z2,z3,z123,z6]),(0,[z166,z1,z2,z730,z5,z6]),(0,[z1,z2,z3,z5,z731,z6]),(0,[z1,z2,z3,z59,z467,z6]),(0,[z1,z2,z3,z20,z6,z480])],[(0,[z17,z1,z2,z3,z254,z6]),(0,[z1,z732,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z436,z6]),(0,[z1,z2,z57,z3,z174,z6])],[(0,[z1,z2,z3,z733,z8,z450]),(0,[z1,z2,z3,z5,z734,z6])],[(0,[z1,z2,z57,z3,z5,z331]),(0,[z1,z2,z735,z3,z5,z8]),(0,[z2,z3,z451,z5,z41,z6])],[(0,[z1,z266,z3,z5,z8,z206]),(0,[z1,z11,z2,z3,z5,z195]),(0,[z116,z1,z736,z3,z5,z6]),(0,[z737,z1,z2,z3,z42,z6])],[(0,[z1,z2,z3,z254,z461,z6])],[(0,[z1,z738,z3,z5,z8,z6]),(0,[z1,z2,z3,z254,z8,z37]),(0,[z1,z2,z3,z739,z5,z6]),(0,[z219,z1,z2,z3,z42,z8]),(0,[z1,z2,z48,z33,z5,z72])],[(0,[z1,z2,z3,z5,z6,z740])],[(0,[z1,z2,z741,z5,z8,z6]),(0,[z137,z11,z139,z3,z5,z6]),(0,[z137,z1,z497,z3,z5,z6]),(0,[z248,z1,z2,z3,z42,z8])],[(0,[z151,z2,z742,z5,z8,z6]),(0,[z1,z2,z3,z5,z743,z6]),(0,[z1,z2,z3,z5,z744,z27]),(0,[z1,z2,z47,z222,z5,z6])],[(0,[z1,z2,z3,z5,z745,z6]),(0,[z1,z2,z3,z746,z5,z6]),(0,[z747,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z21,z331]),(0,[z151,z2,z49,z42,z8,z6]),(0,[z1,z2,z3,z5,z41,z237]),(0,[z1,z2,z3,z5,z748,z6]),(0,[z1,z183,z2,z3,z91,z6])],[(0,[z1,z2,z749,z3,z5,z6]),(0,[z1,z2,z3,z42,z5,z45])],[(0,[z1,z2,z3,z5,z750,z6])],[(0,[z1,z266,z3,z5,z6,z27]),(0,[z1,z2,z751,z3,z5,z6]),(0,[z1,z2,z3,z752,z8,z6]),(0,[z1,z2,z3,z753,z5,z6]),(0,[z219,z1,z2,z3,z106,z5]),(0,[z1,z2,z221,z3,z42,z8]),(0,[z1,z2,z3,z482,z6,z557])],[(0,[z1,z3,z5,z754,z198,z6]),(0,[z1,z2,z3,z5,z755,z6]),(0,[z58,z1,z2,z3,z53,z237]),(0,[z1,z2,z3,z42,z103,z20])],[(0,[z1,z2,z3,z42,z8,z517]),(0,[z1,z2,z3,z756,z8,z6]),(0,[z1,z2,z3,z42,z8,z456])],[(0,[z1,z2,z3,z5,z8,z37]),(0,[z1,z2,z26,z3,z42,z21]),(0,[z1,z2,z3,z128,z41,z6]),(0,[z1,z2,z3,z521,z33,z6]),(0,[z1,z2,z26,z3,z42,z8]),(0,[z590,z1,z2,z3,z42,z27])],[]],
   [[(0,[z1,z2,z57,z3,z314,z6]),(0,[z1,z2,z3,z42,z500,z6]),(0,[z1,z2,z3,z42,z10,z505]),(0,[z1,z2,z3,z757,z5,z6]),(0,[z1,z2,z758,z5,z8,z6]),(0,[z1,z2,z3,z42,z40,z27]),(0,[z197,z1,z2,z3,z482,z6])],[(0,[z1,z2,z3,z759,z8,z6]),(0,[z1,z2,z48,z3,z42,z21]),(0,[z760,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z8,z450]),(0,[z1,z2,z3,z432,z89,z8]),(0,[z1,z761,z2,z3,z5,z6]),(0,[z1,z2,z26,z3,z5,z338])],[(0,[z1,z374,z3,z5,z198,z6])],[(0,[z1,z2,z3,z42,z8,z213]),(0,[z1,z2,z3,z106,z5,z74]),(0,[z1,z25,z2,z3,z42,z308]),(0,[z1,z2,z3,z5,z762,z6]),(0,[z1,z2,z26,z173,z8,z69])],[(0,[z1,z2,z3,z5,z6,z763]),(0,[z1,z629,z2,z3,z42,z8]),(0,[z1,z2,z3,z401,z8,z6]),(0,[z1,z2,z48,z3,z5,z338]),(0,[z1,z2,z3,z547,z42,z27])],[(0,[z2,z49,z742,z5,z8,z6]),(1,[z219,z1,z2,z3,z42]),(0,[z1,z2,z3,z5,z6,z764])],[(0,[z131,z2,z3,z93,z169,z6]),(0,[z1,z2,z3,z5,z765,z6]),(0,[z1,z2,z3,z42,z18,z27])],[(0,[z1,z2,z3,z766,z8,z6]),(0,[z1,z2,z3,z5,z767,z6]),(0,[z1,z2,z3,z42,z6,z27])],[(0,[z1,z2,z3,z42,z94,z6]),(0,[z43,z1,z2,z212,z5,z6]),(0,[z1,z44,z3,z5,z70,z27]),(0,[z441,z1,z2,z3,z76,z6])],[(0,[z1,z2,z3,z768,z8,z6]),(0,[z1,z2,z3,z5,z8,z769])],[(0,[z1,z2,z3,z5,z770,z6]),(0,[z1,z2,z3,z5,z771,z6])],[(0,[z772,z1,z2,z3,z5,z6]),(0,[z43,z1,z2,z3,z5,z773]),(0,[z1,z44,z2,z3,z289,z8]),(0,[z1,z2,z376,z3,z5,z6]),(0,[z1,z2,z3,z42,z6,z480])],[(0,[z2,z152,z3,z503,z5,z6]),(0,[z1,z2,z3,z5,z169,z6]),(0,[z1,z11,z2,z774,z5,z6]),(0,[z775,z1,z2,z3,z42,z6]),(0,[z1,z2,z3,z776,z8,z6])],[(0,[z1,z2,z138,z5,z501,z6]),(0,[z1,z2,z3,z5,z6,z729]),(0,[z17,z1,z2,z3,z482,z6])],[(0,[z1,z2,z35,z5,z500,z6]),(0,[z1,z2,z3,z5,z8,z777]),(0,[z1,z2,z3,z42,z103,z10]),(0,[z116,z1,z2,z125,z5,z6]),(0,[z286,z1,z2,z3,z308,z6])],[(0,[z1,z2,z3,z5,z474,z6]),(0,[z1,z2,z3,z5,z10,z581]),(0,[z17,z1,z56,z3,z89,z6]),(0,[z1,z2,z3,z42,z8,z45]),(0,[z1,z2,z3,z778,z8,z6])],[(0,[z1,z2,z3,z5,z779,z6]),(0,[z1,z2,z3,z780,z5,z6]),(0,[z1,z2,z3,z781,z5,z6]),(0,[z1,z2,z57,z369,z5,z6])],[(0,[z1,z2,z3,z246,z20,z6]),(0,[z1,z2,z3,z294,z20,z6])],[(0,[z1,z2,z3,z5,z782,z6]),(0,[z15,z11,z16,z3,z5,z6]),(0,[z1,z2,z3,z783,z5,z8]),(0,[z1,z25,z11,z3,z5,z97]),(0,[z17,z1,z44,z2,z3,z42])],[(0,[z1,z2,z3,z500,z20,z6]),(0,[z1,z2,z3,z482,z6,z228])],[(0,[z1,z2,z3,z5,z444,z6]),(0,[z1,z2,z3,z5,z754,z6]),(0,[z1,z2,z57,z220,z5,z6]),(0,[z116,z1,z2,z88,z20,z6])],[(0,[z1,z11,z177,z51,z5,z6]),(0,[z350,z17,z1,z2,z3,z42]),(0,[z1,z2,z3,z289,z33,z6])],[(0,[z784,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z785,z6]),(0,[z1,z2,z3,z5,z786,z6]),(0,[z17,z1,z2,z3,z498,z6]),(0,[z1,z2,z787,z42,z8,z6])],[(0,[z129,z2,z3,z5,z8,z788]),(0,[z1,z2,z3,z42,z6,z789]),(0,[z1,z2,z3,z498,z103,z6])],[(0,[z1,z2,z3,z725,z65,z8]),(0,[z1,z2,z384,z40,z8,z6])],[(0,[z790,z1,z2,z3,z5,z6]),(0,[z1,z177,z51,z5,z288,z6]),(0,[z1,z2,z3,z791,z8,z6]),(0,[z1,z792,z2,z3,z5,z6])],[(0,[z1,z218,z3,z5,z97,z6]),(0,[z1,z2,z57,z3,z462,z6]),(0,[z299,z2,z3,z251,z5,z6])],[(0,[z131,z1,z2,z3,z42,z27]),(0,[z1,z2,z3,z42,z21,z18]),(0,[z1,z2,z57,z3,z5,z793]),(0,[z1,z2,z3,z42,z27,z228]),(0,[z1,z183,z2,z3,z20,z6])],[(0,[z1,z2,z794,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z795]),(0,[z1,z796,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z797,z6]),(0,[z1,z2,z3,z20,z6,z581]),(0,[z1,z2,z3,z798,z5,z6]),(0,[z24,z1,z2,z550,z5,z6]),(0,[z1,z799,z2,z3,z5,z6]),(0,[z1,z2,z26,z8,z20,z69])],[(0,[z1,z2,z3,z106,z21,z20]),(0,[z17,z1,z2,z3,z65,z6]),(0,[z1,z2,z431,z57,z5,z6]),(0,[z1,z2,z3,z498,z6,z228]),(0,[z1,z2,z3,z800,z6,z27])]],
   [[(0,[z142,z1,z2,z165,z5,z6]),(0,[z1,z11,z2,z3,z42,z6]),(0,[z1,z2,z3,z42,z70,z27]),(0,[z1,z2,z3,z5,z6,z801])],[(0,[z802,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z169,z80]),(0,[z1,z2,z3,z60,z42,z27]),(0,[z1,z2,z803,z3,z5,z6])],[(0,[z9,z2,z3,z8,z20,z10]),(0,[z1,z2,z804,z3,z5,z6]),(0,[z1,z231,z2,z3,z42,z6]),(0,[z1,z2,z3,z5,z805,z6])],[(0,[z1,z2,z806,z3,z5,z6]),(0,[z1,z2,z3,z5,z807,z6]),(0,[z1,z2,z3,z8,z808,z6])],[(0,[z1,z2,z3,z114,z8,z450]),(0,[z1,z2,z809,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z810]),(0,[z1,z2,z3,z5,z6,z811]),(0,[z1,z2,z3,z33,z5,z302]),(0,[z1,z2,z812,z3,z5,z6])],[(0,[z36,z329,z4,z5,z8,z6]),(0,[z1,z2,z3,z503,z5,z6]),(0,[z1,z2,z57,z550,z5,z6]),(1,[z1,z2,z813,z8,z6])],[(0,[z1,z2,z57,z3,z114,z6]),(0,[z1,z2,z3,z5,z6,z814]),(0,[z1,z2,z815,z3,z5,z6]),(0,[z1,z2,z207,z3,z42,z6]),(0,[z1,z2,z813,z40,z8,z6]),(0,[z1,z2,z3,z33,z5,z237])],[(0,[z17,z1,z490,z3,z5,z6]),(0,[z1,z2,z3,z816,z8,z6]),(0,[z1,z2,z3,z5,z6,z817]),(0,[z347,z2,z3,z5,z41,z6]),(0,[z58,z1,z2,z3,z76,z6]),(0,[z116,z1,z2,z5,z6,z77])],[(0,[z1,z2,z3,z42,z93,z27]),(0,[z170,z1,z2,z3,z98,z6]),(0,[z1,z2,z3,z42,z103,z84]),(0,[z1,z2,z3,z462,z6,z27])],[(0,[z1,z2,z3,z5,z818,z6]),(0,[z1,z2,z57,z3,z5,z68]),(0,[z1,z2,z3,z42,z5,z789])],[(0,[z1,z2,z3,z5,z8,z819]),(0,[z1,z2,z3,z409,z103,z6]),(0,[z820,z1,z2,z3,z5,z6])],[(0,[z1,z329,z3,z5,z41,z6]),(0,[z1,z2,z5,z6,z821,z228]),(0,[z2,z3,z5,z6,z84,z557]),(0,[z1,z2,z212,z3,z20,z6]),(0,[z116,z1,z2,z3,z822,z6]),(0,[z1,z2,z3,z823,z20,z6])],[(0,[z1,z2,z3,z5,z824,z6]),(0,[z825,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z20,z826,z6]),(0,[z1,z3,z5,z8,z6,z769])],[(0,[z17,z151,z2,z49,z5,z6]),(0,[z1,z25,z3,z33,z5,z97])],[(0,[z1,z2,z3,z42,z359,z6]),(0,[z1,z2,z3,z87,z5,z581]),(0,[z1,z2,z3,z827,z5,z8])],[(0,[z1,z2,z165,z49,z5,z6]),(0,[z1,z2,z3,z5,z828,z6]),(0,[z1,z2,z100,z101,z21,z6]),(0,[z1,z2,z3,z41,z464,z6]),(1,[z1,z2,z3,z725,z8]),(0,[z1,z11,z2,z3,z174,z6]),(0,[z17,z1,z2,z3,z419,z6]),(0,[z1,z2,z3,z33,z5,z232]),(0,[z1,z2,z3,z42,z33,z27])],[(0,[z15,z16,z3,z5,z8,z6]),(0,[z1,z86,z2,z3,z20,z6]),(0,[z1,z2,z3,z5,z41,z195]),(0,[z1,z2,z3,z5,z829,z6]),(0,[z1,z2,z3,z830,z8,z6]),(0,[z1,z2,z3,z33,z831,z6])],[(0,[z1,z11,z2,z3,z5,z331]),(0,[z1,z832,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z21,z68]),(0,[z1,z2,z3,z42,z563,z6]),(0,[z1,z11,z665,z3,z5,z6]),(0,[z116,z1,z2,z3,z208,z5]),(1,[z1,z2,z3,z42,z157]),(0,[z1,z2,z3,z42,z27,z27])],[(0,[z1,z2,z57,z263,z5,z6]),(0,[z1,z11,z2,z3,z833,z6])],[(0,[z1,z374,z16,z3,z5,z6]),(0,[z1,z2,z3,z834,z8,z6]),(0,[z1,z2,z3,z464,z6,z27])],[(0,[z1,z2,z138,z5,z500,z6]),(0,[z1,z2,z3,z835,z5,z6]),(0,[z116,z1,z2,z100,z101,z6]),(0,[z1,z2,z3,z498,z6,z27])],[(0,[z1,z2,z3,z8,z836,z6]),(0,[z7,z1,z2,z3,z20,z6]),(0,[z116,z1,z2,z5,z229,z6]),(0,[z82,z86,z2,z3,z5,z6]),(0,[z1,z2,z3,z462,z53,z6])],[(0,[z219,z1,z2,z3,z837,z6])],[(0,[z1,z2,z3,z5,z6,z838]),(0,[z1,z2,z3,z5,z8,z839]),(0,[z2,z3,z42,z8,z10,z84]),(0,[z1,z2,z3,z281,z8,z6]),(0,[z1,z183,z3,z5,z149,z6])],[(0,[z137,z139,z3,z42,z8,z6]),(0,[z1,z2,z3,z5,z130,z27]),(0,[z1,z2,z3,z5,z103,z6])],[(0,[z1,z2,z3,z402,z5,z27]),(0,[z1,z2,z3,z462,z5,z27])],[(0,[z1,z56,z57,z3,z89,z6])],[(0,[z17,z1,z329,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z840]),(0,[z1,z2,z841,z3,z5,z6])],[(0,[z1,z2,z138,z5,z6,z27]),(0,[z1,z2,z3,z8,z842,z6]),(0,[z1,z843,z2,z3,z5,z6]),(0,[z28,z2,z3,z92,z41,z6]),(0,[z1,z2,z844,z3,z5,z6]),(0,[z1,z2,z26,z165,z5,z6]),(0,[z116,z1,z2,z276,z5,z6])],[(0,[z1,z2,z3,z42,z6,z581])],[(0,[z845,z1,z329,z3,z5,z6]),(0,[z1,z2,z3,z5,z846,z6])],[(0,[z1,z2,z3,z5,z6,z228]),(0,[z1,z2,z3,z5,z6,z505])]],
   [[(0,[z1,z2,z3,z5,z334,z195]),(0,[z1,z2,z3,z8,z19,z80]),(0,[z1,z847,z3,z5,z8,z6]),(0,[z1,z2,z848,z3,z5,z6]),(0,[z1,z44,z3,z5,z344,z70]),(0,[z1,z2,z3,z42,z8,z789])],[(0,[z1,z2,z3,z849,z5,z6]),(0,[z17,z1,z2,z3,z850,z6]),(0,[z17,z1,z176,z3,z5,z6]),(0,[z1,z2,z3,z256,z5,z27])],[(0,[z1,z2,z3,z42,z246,z6]),(0,[z17,z1,z2,z3,z851,z6])],[(0,[z116,z1,z2,z3,z5,z195]),(0,[z1,z852,z2,z3,z5,z6]),(0,[z1,z218,z3,z5,z198,z6]),(0,[z1,z2,z3,z853,z5,z6]),(0,[z1,z11,z2,z3,z42,z10]),(0,[z1,z544,z2,z3,z42,z8])],[(0,[z151,z2,z49,z5,z8,z6]),(0,[z1,z2,z3,z42,z29,z6]),(0,[z1,z2,z854,z3,z5,z6]),(0,[z1,z2,z3,z855,z5,z6])],[(0,[z36,z2,z4,z8,z20,z6]),(0,[z856,z1,z2,z3,z5,z6]),(0,[z116,z1,z857,z3,z5,z6]),(0,[z1,z2,z3,z5,z380,z27])],[(0,[z17,z1,z2,z3,z104,z6]),(0,[z1,z2,z858,z5,z6,z228]),(0,[z1,z2,z3,z42,z33,z20])],[(0,[z137,z139,z35,z5,z8,z6]),(0,[z1,z44,z3,z5,z41,z70]),(0,[z1,z2,z3,z5,z6,z859]),(0,[z1,z2,z26,z5,z430,z69]),(0,[z1,z2,z3,z5,z860,z6])],[(0,[z1,z2,z3,z114,z501,z6]),(0,[z1,z2,z3,z462,z34,z6])],[(0,[z1,z2,z3,z254,z6,z27]),(0,[z1,z2,z607,z3,z42,z8])],[(0,[z1,z2,z3,z5,z8,z206]),(0,[z1,z2,z3,z254,z94,z6]),(0,[z1,z2,z3,z5,z6,z861]),(0,[z1,z2,z3,z143,z20,z6]),(0,[z1,z2,z3,z5,z8,z862])],[(0,[z1,z2,z3,z5,z863,z6]),(0,[z541,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z63,z6,z157]),(0,[z1,z2,z3,z864,z33,z6])],[(0,[z1,z2,z385,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z865]),(0,[z1,z2,z57,z3,z5,z37]),(0,[z1,z2,z3,z5,z6,z866]),(0,[z1,z867,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z868,z6]),(0,[z1,z2,z3,z120,z34,z6])],[(0,[z869,z1,z2,z3,z5,z6]),(0,[z1,z180,z3,z5,z149,z6]),(0,[z1,z2,z3,z870,z5,z6])],[(0,[z1,z2,z138,z314,z8,z6]),(0,[z1,z218,z2,z3,z5,z6]),(0,[z131,z2,z3,z93,z6,z27]),(0,[z1,z2,z3,z42,z5,z581]),(0,[z1,z2,z3,z462,z359,z6])],[(0,[z166,z1,z2,z3,z42,z6]),(0,[z871,z1,z2,z3,z5,z6]),(0,[z466,z1,z2,z3,z208,z5])],[(0,[z1,z2,z57,z3,z5,z450]),(0,[z1,z2,z3,z872,z5,z6]),(0,[z1,z2,z3,z873,z5,z6]),(0,[z1,z2,z3,z462,z8,z27])],[(0,[z1,z2,z3,z752,z21,z6]),(0,[z1,z2,z3,z5,z874,z6]),(0,[z1,z2,z3,z875,z5,z6])],[(0,[z1,z2,z876,z5,z8,z6]),(0,[z1,z2,z3,z5,z84,z74]),(0,[z1,z2,z3,z42,z432,z8]),(0,[z1,z2,z261,z547,z8,z6])],[(0,[z17,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z877,z8,z6]),(0,[z1,z2,z878,z5,z8,z6]),(0,[z137,z186,z139,z3,z5,z6]),(0,[z1,z2,z3,z5,z879,z6]),(0,[z1,z2,z3,z289,z8,z84]),(0,[z1,z177,z51,z33,z5,z6]),(0,[z1,z2,z3,z419,z6,z27])],[(0,[z1,z2,z3,z5,z6,z27]),(0,[z1,z2,z3,z5,z880,z6]),(0,[z1,z2,z3,z5,z21,z37]),(0,[z1,z2,z3,z5,z6,z881]),(0,[z1,z2,z57,z633,z5,z6]),(0,[z1,z2,z3,z5,z882,z6]),(0,[z1,z2,z3,z208,z5,z27]),(0,[z1,z2,z3,z883,z5,z6]),(0,[z1,z2,z3,z498,z34,z6])],[(0,[z407,z16,z3,z5,z8,z6]),(0,[z1,z2,z3,z884,z5,z6]),(0,[z107,z2,z3,z251,z5,z6])],[(0,[z845,z1,z2,z3,z5,z6]),(0,[z420,z2,z3,z92,z8,z6]),(0,[z1,z2,z165,z3,z20,z6]),(1,[z1,z2,z5,z771,z6]),(0,[z1,z885,z2,z3,z5,z6])],[(0,[z1,z2,z3,z886,z5,z6]),(0,[z1,z2,z3,z887,z5,z6]),(0,[z1,z2,z3,z409,z5,z27])],[(0,[z1,z2,z3,z5,z21,z450]),(0,[z1,z2,z3,z42,z339,z27])],[(0,[z1,z2,z3,z8,z20,z331]),(0,[z1,z329,z3,z33,z5,z6]),(0,[z1,z2,z3,z888,z5,z6])],[(0,[z1,z2,z3,z123,z474,z6]),(0,[z1,z2,z3,z5,z6,z889]),(0,[z1,z2,z890,z3,z5,z6]),(0,[z1,z2,z891,z42,z8,z6]),(0,[z1,z2,z3,z42,z308,z18]),(0,[z1,z2,z3,z42,z103,z187])],[(0,[z1,z2,z3,z401,z21,z6]),(0,[z1,z44,z11,z3,z5,z70])],[(0,[z1,z11,z2,z3,z462,z6])],[(0,[z892,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z893,z6]),(0,[z9,z2,z3,z5,z10,z27]),(0,[z1,z2,z3,z894,z8,z6]),(0,[z1,z2,z3,z5,z895,z6])],[(0,[z1,z2,z3,z5,z6,z896]),(0,[z17,z1,z2,z3,z67,z6]),(0,[z1,z2,z220,z3,z42,z8])],[(0,[z1,z2,z3,z8,z464,z195])]],
   [[(0,[z1,z2,z897,z3,z5,z6]),(0,[z1,z2,z3,z332,z5,z581]),(0,[z898,z1,z2,z3,z5,z6]),(0,[z1,z2,z57,z5,z558,z6]),(0,[z1,z2,z3,z42,z870,z6]),(0,[z1,z2,z3,z42,z103,z168]),(0,[z1,z2,z899,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z900]),(0,[z1,z2,z3,z5,z6,z901]),(0,[z1,z2,z902,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z903])],[(0,[z1,z2,z3,z8,z904,z6]),(0,[z1,z266,z4,z5,z8,z6]),(0,[z1,z51,z905,z5,z8,z6]),(0,[z1,z2,z3,z5,z906,z6])],[(0,[z17,z1,z11,z3,z42,z6])],[(0,[z1,z2,z3,z907,z8,z6]),(0,[z1,z266,z3,z42,z8,z6])],[(0,[z1,z2,z3,z42,z8,z581]),(0,[z1,z2,z3,z42,z908,z6])],[(0,[z1,z2,z3,z314,z8,z6]),(0,[z1,z497,z3,z5,z6,z70])],[(0,[z1,z11,z2,z3,z114,z6]),(0,[z1,z2,z3,z8,z909,z206]),(0,[z17,z1,z2,z3,z5,z80]),(0,[z1,z2,z3,z5,z910,z6])],[(0,[z116,z1,z177,z51,z5,z6]),(0,[z1,z2,z3,z8,z20,z335]),(0,[z1,z25,z2,z3,z42,z33])],[(0,[z1,z2,z3,z911,z8,z6]),(0,[z142,z1,z2,z3,z281,z6]),(0,[z1,z2,z3,z42,z554,z6]),(0,[z1,z11,z2,z26,z3,z42]),(0,[z1,z2,z3,z106,z20,z27]),(0,[z1,z2,z3,z850,z6,z27])],[(0,[z912,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z773]),(0,[z1,z11,z2,z3,z5,z68])],[(0,[z148,z2,z3,z5,z710,z6]),(0,[z1,z2,z3,z5,z337,z6]),(0,[z1,z2,z913,z3,z5,z6])],[(0,[z137,z139,z138,z5,z8,z6]),(0,[z1,z2,z3,z418,z33,z5]),(0,[z1,z2,z3,z33,z91,z6])],[(0,[z1,z2,z3,z343,z5,z41]),(0,[z1,z2,z3,z914,z6,z411])],[(0,[z1,z2,z3,z114,z500,z6]),(0,[z1,z2,z3,z915,z5,z6]),(0,[z2,z742,z4,z5,z8,z6]),(0,[z2,z3,z565,z5,z41,z6]),(0,[z916,z2,z3,z5,z8,z6]),(0,[z211,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z5,z6,z917])],[(0,[z1,z2,z3,z918,z8,z6]),(0,[z1,z919,z2,z3,z5,z6]),(0,[z219,z1,z2,z3,z5,z380]),(0,[z1,z2,z3,z256,z8,z20])],[(0,[z1,z2,z3,z20,z6,z920]),(0,[z921,z1,z2,z3,z5,z6])],[(0,[z24,z1,z2,z3,z5,z819]),(0,[z1,z2,z3,z5,z922,z6]),(0,[z1,z2,z57,z3,z432,z5]),(0,[z1,z2,z3,z42,z5,z557])],[(0,[z1,z2,z3,z5,z6,z923]),(0,[z1,z2,z3,z5,z8,z924]),(0,[z1,z925,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z33,z84]),(0,[z116,z1,z2,z3,z42,z6]),(0,[z1,z2,z3,z362,z5,z6]),(0,[z1,z2,z217,z3,z42,z8])],[(0,[z1,z218,z16,z3,z5,z6]),(0,[z1,z2,z3,z33,z215,z6]),(0,[z1,z2,z3,z42,z149,z27]),(0,[z1,z2,z3,z5,z926,z6])],[(0,[z1,z2,z3,z5,z927,z6]),(0,[z1,z2,z3,z928,z8,z6]),(0,[z1,z2,z3,z42,z8,z367])],[(0,[z1,z44,z3,z33,z5,z70]),(0,[z1,z2,z3,z33,z112,z6])],[(0,[z1,z2,z3,z114,z6,z27]),(0,[z1,z2,z3,z174,z21,z6]),(0,[z249,z1,z2,z165,z5,z6]),(0,[z1,z2,z3,z929,z8,z6]),(0,[z1,z2,z3,z5,z930,z6])],[(0,[z1,z2,z3,z5,z377,z6]),(0,[z1,z2,z3,z931,z8,z6])],[(0,[z1,z2,z57,z3,z5,z819]),(0,[z932,z2,z3,z42,z8,z6])],[(0,[z1,z2,z3,z42,z933,z6]),(0,[z111,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z934,z5,z6]),(0,[z1,z2,z3,z5,z935,z6])],[(0,[z1,z622,z2,z3,z42,z8]),(0,[z1,z2,z57,z3,z5,z936])],[(0,[z443,z1,z139,z3,z5,z6]),(0,[z1,z678,z3,z89,z8,z6]),(0,[z1,z2,z3,z5,z73,z6]),(0,[z1,z2,z3,z343,z5,z423])],[(0,[z1,z2,z3,z5,z937,z6]),(0,[z1,z2,z3,z5,z938,z6]),(0,[z1,z2,z3,z939,z5,z6])],[],[(0,[z15,z16,z57,z3,z5,z6]),(0,[z1,z2,z940,z3,z5,z6]),(0,[z1,z2,z3,z941,z5,z6]),(0,[z1,z2,z101,z813,z8,z6])],[(0,[z1,z2,z3,z418,z92,z8]),(0,[z1,z2,z3,z33,z942,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z773]),(0,[z1,z2,z3,z943,z8,z6]),(0,[z1,z2,z3,z42,z944,z6]),(0,[z1,z2,z3,z106,z5,z157]),(0,[z1,z2,z730,z5,z6,z27])],[(0,[z1,z2,z3,z945,z5,z6]),(0,[z1,z2,z3,z5,z158,z6]),(0,[z2,z3,z5,z524,z41,z6]),(0,[z116,z1,z2,z3,z174,z6]),(0,[z1,z2,z3,z946,z5,z6]),(0,[z1,z2,z3,z5,z947,z6]),(0,[z1,z2,z217,z3,z20,z6])],[(0,[z948,z1,z2,z3,z5,z6]),(0,[z1,z86,z3,z5,z468,z6]),(0,[z443,z1,z11,z3,z5,z6]),(0,[z1,z56,z2,z3,z42,z27]),(0,[z1,z2,z3,z5,z6,z949])],[(0,[z116,z1,z2,z3,z5,z331]),(0,[z1,z2,z3,z950,z21,z6]),(0,[z1,z2,z3,z5,z951,z6]),(0,[z1,z2,z3,z42,z8,z952]),(0,[z197,z1,z2,z3,z42,z27])],[(0,[z1,z497,z3,z5,z198,z6]),(0,[z1,z2,z3,z432,z33,z5]),(0,[z1,z2,z3,z20,z6,z953])],[(0,[z1,z2,z57,z235,z5,z6]),(0,[z1,z2,z3,z33,z5,z338]),(0,[z1,z2,z3,z954,z174,z6])],[(0,[z15,z16,z3,z5,z21,z6]),(0,[z1,z2,z3,z343,z5,z8])],[(0,[z1,z2,z3,z5,z206,z27]),(0,[z1,z2,z858,z3,z5,z6]),(0,[z148,z1,z2,z3,z42,z27]),(0,[z1,z2,z955,z3,z5,z6]),(0,[z1,z2,z3,z33,z956,z6])],[(0,[z1,z2,z3,z42,z8,z646]),(0,[z9,z1,z2,z3,z42,z27]),(0,[z17,z1,z2,z3,z957,z6]),(0,[z1,z2,z3,z33,z5,z18])],[(0,[z1,z2,z3,z5,z958,z6]),(0,[z1,z2,z3,z14,z20,z6]),(0,[z1,z2,z3,z5,z959,z6])],[(0,[z1,z2,z3,z5,z960,z6]),(0,[z1,z2,z3,z5,z961,z6])],[(0,[z116,z28,z2,z3,z92,z6])],[(0,[z15,z738,z3,z5,z8,z6]),(0,[z107,z2,z196,z3,z5,z6]),(0,[z116,z1,z962,z3,z5,z6]),(0,[z1,z2,z3,z42,z656,z6])],[(0,[z1,z11,z2,z3,z5,z37]),(0,[z1,z2,z3,z281,z21,z6]),(0,[z1,z2,z207,z5,z72,z6]),(0,[z1,z2,z3,z33,z128,z6]),(0,[z1,z2,z3,z498,z482,z6])],[(0,[z1,z2,z3,z5,z963,z6]),(0,[z1,z2,z3,z463,z5,z27])],[(0,[z1,z2,z964,z3,z5,z6]),(0,[z1,z497,z2,z3,z5,z6]),(0,[z1,z2,z965,z42,z8,z6])],[(0,[z466,z1,z2,z3,z42,z6])],[(0,[z1,z11,z2,z3,z5,z450]),(0,[z17,z1,z2,z3,z42,z27])],[(0,[z166,z1,z497,z3,z5,z6]),(0,[z966,z1,z2,z3,z5,z6])],[(0,[z116,z1,z2,z3,z314,z6])],[(0,[z1,z329,z3,z5,z461,z6]),(0,[z967,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z41,z18]),(0,[z1,z177,z51,z8,z20,z6]),(0,[z1,z2,z3,z5,z6,z968])],[(0,[z1,z2,z3,z969,z8,z6]),(0,[z1,z329,z3,z5,z8,z37]),(0,[z36,z1,z2,z217,z5,z6]),(0,[z166,z1,z2,z758,z5,z6]),(0,[z1,z2,z3,z970,z128,z6]),(0,[z1,z2,z3,z42,z20,z157]),(0,[z1,z2,z3,z971,z20,z6])],[(0,[z1,z2,z3,z5,z972,z6]),(0,[z1,z2,z3,z5,z973,z6]),(0,[z1,z847,z3,z5,z21,z6]),(0,[z1,z2,z3,z974,z5,z6]),(0,[z1,z2,z3,z975,z5,z6]),(0,[z1,z2,z3,z976,z8,z6])],[(0,[z1,z2,z3,z5,z977,z6]),(0,[z1,z2,z3,z432,z92,z8]),(0,[z978,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z979,z6]),(0,[z1,z2,z3,z851,z6,z310]),(0,[z1,z2,z3,z5,z826,z6]),(0,[z1,z2,z3,z375,z5,z68])],[(0,[z1,z2,z57,z3,z5,z206]),(0,[z1,z2,z3,z5,z980,z6]),(0,[z1,z2,z100,z227,z101,z6])],[(0,[z36,z2,z4,z104,z8,z6]),(0,[z437,z2,z3,z5,z21,z6]),(0,[z24,z1,z2,z3,z931,z6])],[(0,[z981,z1,z2,z3,z5,z6]),(0,[z151,z2,z49,z5,z21,z6]),(0,[z1,z2,z3,z5,z6,z982])],[(0,[z1,z2,z3,z461,z20,z6]),(0,[z116,z131,z2,z3,z93,z6]),(0,[z1,z204,z374,z3,z5,z6]),(0,[z983,z1,z2,z3,z5,z6])],[(0,[z984,z1,z2,z3,z5,z6]),(0,[z1,z985,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z986,z6]),(0,[z1,z2,z3,z20,z6,z987])],[(0,[z1,z2,z3,z988,z8,z6]),(0,[z989,z1,z2,z3,z5,z6]),(0,[z1,z2,z858,z5,z6,z84]),(0,[z1,z2,z3,z123,z6,z27]),(0,[z590,z2,z3,z5,z8,z10]),(0,[z1,z2,z212,z5,z88,z6])],[(0,[z365,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z41,z990])]],
   [[(0,[z1,z2,z3,z5,z287,z6]),(0,[z1,z2,z3,z5,z21,z206]),(0,[z1,z991,z3,z5,z8,z6]),(0,[z1,z2,z3,z992,z5,z8]),(0,[z1,z2,z57,z3,z931,z6])],[(0,[z1,z2,z993,z3,z5,z6]),(0,[z1,z2,z3,z994,z5,z6]),(0,[z995,z1,z2,z3,z5,z6]),(0,[z1,z2,z996,z3,z5,z6]),(0,[z1,z44,z3,z5,z436,z70]),(0,[z1,z44,z2,z57,z3,z42]),(0,[z1,z2,z57,z3,z976,z6])],[(0,[z1,z2,z3,z5,z500,z331]),(0,[z1,z2,z3,z997,z8,z6])],[(0,[z1,z2,z3,z5,z998,z6]),(0,[z1,z2,z3,z999,z8,z6]),(0,[z1,z2,z3,z5,z8,z1000]),(0,[z116,z1,z2,z57,z20,z6]),(0,[z1,z2,z3,z831,z8,z6])],[(0,[z1,z2,z3,z42,z423,z6]),(0,[z1,z2,z3,z42,z33,z187])],[(0,[z1,z266,z3,z254,z8,z6]),(0,[z1,z2,z3,z5,z1001,z6]),(0,[z1,z2,z3,z5,z1002,z6]),(0,[z219,z1,z2,z48,z3,z42]),(0,[z1,z2,z1003,z3,z5,z6])],[(0,[z137,z139,z3,z114,z8,z6]),(0,[z1004,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z27,z187]),(0,[z1,z2,z3,z359,z91,z6])],[(0,[z17,z1,z2,z35,z5,z6]),(0,[z1,z2,z1005,z3,z5,z6]),(0,[z28,z2,z3,z252,z8,z6]),(0,[z148,z2,z3,z5,z6,z557]),(0,[z1,z2,z100,z101,z41,z6]),(0,[z1,z2,z3,z5,z1006,z6])],[(0,[z1,z2,z3,z5,z8,z1007]),(0,[z1,z2,z3,z42,z8,z669]),(0,[z9,z2,z3,z5,z6,z557]),(0,[z1,z2,z3,z5,z8,z773]),(0,[z17,z1,z2,z3,z42,z20]),(0,[z1,z2,z3,z1008,z8,z6]),(0,[z1,z2,z3,z488,z5,z6])],[(0,[z1,z2,z3,z5,z169,z195]),(0,[z1,z2,z3,z5,z41,z68]),(0,[z1,z442,z2,z3,z42,z8]),(0,[z1,z11,z2,z3,z20,z6])],[(0,[z1,z2,z3,z1009,z5,z6]),(0,[z1,z2,z3,z5,z1010,z6])],[(0,[z43,z1,z2,z3,z42,z27]),(0,[z1,z231,z2,z3,z20,z6]),(0,[z166,z1,z2,z3,z5,z130]),(0,[z1,z2,z3,z42,z8,z546])],[(0,[z142,z1,z2,z3,z65,z6]),(0,[z1,z25,z2,z3,z289,z8]),(0,[z1,z2,z3,z20,z1011,z6]),(0,[z219,z1,z2,z3,z482,z6])],[(0,[z116,z1,z44,z3,z5,z70]),(0,[z1,z2,z3,z42,z1012,z6])],[(0,[z1,z2,z3,z33,z314,z6]),(0,[z116,z1,z2,z3,z462,z6]),(0,[z1,z2,z3,z5,z1013,z6]),(0,[z1,z2,z3,z42,z59,z27])],[(0,[z1,z1014,z2,z3,z5,z6]),(0,[z1,z2,z3,z1015,z8,z37])],[(0,[z1,z1016,z3,z5,z8,z6]),(0,[z1,z56,z3,z253,z8,z6]),(0,[z1,z2,z3,z5,z1017,z6]),(0,[z1,z226,z2,z3,z42,z8])],[(0,[z1,z2,z3,z1018,z5,z6]),(0,[z1,z2,z3,z42,z101,z27]),(0,[z1,z2,z3,z33,z106,z20])],[(0,[z1,z11,z2,z3,z432,z5])],[(0,[z1,z2,z3,z554,z5,z6]),(0,[z1,z2,z3,z5,z1019,z6]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z1,z2,z3,z488,z67,z6]),(0,[z1,z2,z47,z3,z462,z6])],[(0,[z1,z2,z3,z5,z713,z6])],[(0,[z1,z2,z3,z8,z20,z37]),(0,[z1,z2,z49,z212,z5,z6]),(0,[z1021,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1022,z5,z6]),(0,[z1,z2,z3,z42,z8,z1023]),(0,[z219,z1,z2,z3,z498,z6])],[(0,[z17,z129,z2,z3,z5,z84]),(0,[z1,z2,z3,z5,z1024,z6]),(0,[z1,z2,z376,z3,z91,z6])],[(0,[z1,z2,z3,z1025,z5,z6]),(0,[z17,z1,z2,z3,z5,z237])],[(0,[z1,z486,z2,z3,z42,z8]),(0,[z1,z2,z3,z1026,z8,z6]),(0,[z1,z2,z3,z308,z20,z6])],[(0,[z116,z1,z2,z3,z114,z6]),(0,[z1,z2,z3,z8,z20,z450]),(0,[z137,z231,z2,z3,z5,z6]),(0,[z1027,z1,z2,z3,z5,z6]),(0,[z1,z11,z2,z3,z5,z819])],[(0,[z1,z2,z3,z1028,z5,z6])],[(0,[z1,z2,z1029,z3,z5,z6]),(0,[z116,z1,z2,z26,z3,z42])],[(0,[z1,z2,z3,z314,z21,z6]),(0,[z1,z2,z1030,z3,z5,z6]),(0,[z916,z2,z57,z3,z5,z6]),(0,[z116,z1,z2,z3,z5,z68]),(0,[z1,z2,z3,z42,z488,z6]),(0,[z1,z2,z3,z33,z401,z6])],[(0,[z1,z2,z3,z42,z8,z6]),(0,[z7,z1,z2,z207,z5,z6])],[(0,[z1,z2,z3,z42,z8,z643]),(0,[z153,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z78,z6]),(0,[z1,z2,z3,z42,z8,z459])],[(0,[z1,z44,z2,z3,z42,z21]),(0,[z1,z2,z3,z147,z5,z230]),(0,[z1,z2,z3,z1031,z8,z6]),(0,[z1,z44,z2,z3,z42,z8])]],
   [[(0,[z66,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z8,z1032,z6])],[(0,[z231,z16,z2,z3,z5,z6]),(0,[z687,z2,z3,z5,z8,z84]),(0,[z612,z1,z2,z3,z42,z8]),(0,[z17,z1,z3,z149,z20,z6])],[(0,[z1,z2,z152,z3,z20,z6])],[(0,[z1,z2,z3,z1033,z5,z6]),(0,[z17,z15,z16,z3,z5,z6]),(0,[z1,z266,z49,z5,z8,z6]),(0,[z1,z2,z3,z5,z21,z1034]),(0,[z1,z2,z3,z361,z20,z6]),(0,[z1,z2,z3,z91,z8,z6])],[(0,[z932,z2,z3,z5,z8,z6]),(0,[z1,z2,z71,z432,z40,z8])],[(0,[z1,z2,z1035,z5,z8,z6]),(0,[z1,z2,z3,z5,z1036,z6]),(0,[z1,z2,z3,z123,z73,z6])],[(0,[z1,z2,z57,z3,z1037,z6]),(0,[z1,z2,z3,z42,z1038,z6])],[],[],[(0,[z1,z2,z3,z5,z1039,z6]),(0,[z1,z2,z3,z8,z1040,z6]),(0,[z1,z2,z3,z1041,z5,z6]),(0,[z166,z1,z2,z3,z42,z8]),(0,[z1,z2,z57,z3,z1026,z6]),(0,[z1,z2,z26,z57,z5,z69]),(0,[z1,z2,z3,z1042,z33,z6])],[(0,[z1,z2,z3,z5,z8,z1043]),(0,[z1,z2,z3,z4,z42,z27]),(0,[z1,z2,z3,z1044,z5,z6]),(0,[z1,z2,z3,z359,z20,z6]),(0,[z1045,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z120,z5,z6])],[],[(0,[z1,z2,z35,z5,z8,z6]),(0,[z1,z2,z3,z5,z41,z37])],[(1,[z1,z847,z3,z5,z6]),(0,[z17,z1,z531,z3,z5,z6]),(0,[z1,z2,z3,z344,z20,z6]),(0,[z1,z2,z3,z33,z1046,z6])],[(0,[z1,z56,z11,z3,z89,z6]),(0,[z142,z1,z176,z3,z5,z6]),(0,[z1,z2,z3,z1047,z20,z6]),(0,[z1,z2,z3,z1048,z20,z6])],[(0,[z137,z738,z3,z5,z8,z6]),(0,[z1,z2,z3,z418,z5,z41]),(0,[z1,z2,z3,z5,z6,z1049])],[(0,[z1,z2,z3,z5,z41,z450]),(0,[z1,z2,z3,z1050,z8,z6]),(0,[z1,z2,z3,z5,z1051,z6]),(0,[z1052,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z184,z34,z6]),(0,[z116,z1,z2,z5,z484,z6])],[(0,[z28,z11,z2,z3,z92,z6]),(0,[z1,z2,z3,z42,z8,z80]),(0,[z1,z2,z3,z1053,z5,z6]),(0,[z1,z2,z3,z42,z8,z649]),(0,[z166,z1,z2,z3,z106,z5])],[(0,[z1,z2,z3,z8,z1054,z6]),(0,[z1,z2,z3,z1055,z5,z6]),(0,[z1,z2,z3,z1056,z5,z6]),(0,[z1,z2,z3,z5,z1057,z6]),(0,[z1,z2,z3,z5,z1058,z6])],[(0,[z1,z2,z3,z401,z41,z6]),(0,[z58,z1,z2,z3,z91,z6]),(0,[z1,z2,z3,z482,z68,z27])],[(0,[z1,z1059,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z1060,z6]),(0,[z17,z1,z2,z3,z42,z84]),(1,[z1,z905,z5,z8,z6])],[(0,[z1,z2,z3,z631,z5,z27]),(0,[z1,z2,z3,z65,z8,z6]),(0,[z17,z1,z105,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1061,z6]),(0,[z1,z2,z3,z33,z464,z6])],[(0,[z1,z1062,z2,z3,z5,z6]),(0,[z1,z722,z2,z3,z5,z6]),(0,[z1,z2,z376,z3,z42,z6])],[(0,[z1,z2,z3,z5,z8,z1063]),(0,[z166,z1,z2,z3,z20,z6]),(0,[z17,z1,z2,z71,z40,z6]),(0,[z1,z2,z3,z5,z656,z6])],[(0,[z1,z11,z2,z3,z5,z206]),(0,[z24,z1,z2,z3,z281,z6]),(0,[z1,z374,z2,z3,z42,z6]),(0,[z1,z2,z48,z3,z42,z103])],[(0,[z137,z139,z3,z5,z8,z331]),(0,[z1,z2,z3,z79,z5,z6]),(0,[z1,z2,z3,z1064,z20,z6]),(0,[z1,z2,z3,z1065,z8,z6]),(0,[z1,z2,z3,z1066,z343,z5]),(1,[z1,z2,z3,z8,z1023])],[(0,[z1,z2,z3,z5,z6,z920]),(0,[z1067,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z1068,z6]),(0,[z1,z2,z613,z57,z5,z6])],[(0,[z443,z1,z16,z3,z5,z6]),(0,[z1,z2,z3,z1069,z5,z6]),(0,[z1,z2,z26,z261,z42,z8]),(0,[z1,z2,z47,z3,z91,z6])],[(0,[z1,z2,z3,z462,z8,z6])],[(0,[z1,z2,z100,z165,z5,z6]),(0,[z1,z25,z2,z3,z42,z27]),(0,[z1,z2,z3,z1070,z5,z6])],[(0,[z116,z1,z2,z3,z5,z37]),(0,[z116,z1,z2,z3,z834,z6])]],
   [[(0,[z1,z2,z57,z3,z281,z6])],[(0,[z1,z329,z3,z5,z8,z206]),(0,[z1,z1071,z2,z3,z5,z6]),(0,[z1072,z2,z3,z5,z8,z6]),(0,[z1,z11,z2,z3,z931,z6]),(0,[z1,z2,z3,z5,z6,z1073]),(0,[z1,z2,z3,z8,z851,z6]),(0,[z116,z1,z722,z3,z5,z6])],[],[(0,[z116,z1,z2,z3,z5,z450]),(0,[z36,z2,z79,z4,z5,z6])],[(0,[z1,z2,z3,z42,z42,z27])],[(0,[z1,z180,z139,z3,z5,z6]),(0,[z1,z177,z51,z5,z6,z27]),(0,[z1,z2,z3,z42,z27,z96])],[(0,[z1,z2,z57,z138,z5,z6]),(0,[z382,z1,z2,z49,z5,z6]),(0,[z1,z2,z3,z5,z1074,z6]),(0,[z1,z2,z3,z5,z1075,z6]),(0,[z1076,z2,z3,z42,z8,z6])],[(0,[z1,z2,z3,z432,z5,z41]),(0,[z1,z2,z3,z106,z128,z8]),(0,[z1,z2,z556,z3,z467,z6])],[(0,[z1,z2,z3,z5,z6,z1077]),(0,[z1,z2,z3,z5,z6,z1078]),(0,[z1,z2,z3,z42,z8,z108]),(0,[z1,z56,z3,z33,z89,z6]),(0,[z1,z2,z3,z418,z5,z8]),(0,[z1,z2,z3,z87,z5,z74])],[(0,[z1,z2,z3,z1079,z5,z6]),(0,[z1,z2,z57,z3,z289,z6])],[(0,[z1,z2,z3,z5,z1080,z6]),(0,[z151,z1,z2,z217,z5,z6]),(0,[z1,z2,z3,z42,z8,z259])],[(0,[z1,z2,z1081,z3,z8,z6]),(0,[z1,z329,z3,z5,z6,z27]),(0,[z1,z191,z25,z3,z5,z97]),(0,[z1,z1082,z2,z3,z5,z6])],[(0,[z1,z16,z2,z3,z42,z27]),(0,[z24,z1,z2,z212,z5,z6]),(0,[z1,z2,z3,z1083,z8,z6]),(0,[z17,z1,z11,z3,z20,z6])],[(0,[z1,z2,z3,z1084,z8,z6]),(1,[z2,z3,z5,z710,z6]),(0,[z82,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z6,z1085]),(0,[z1,z2,z3,z308,z103,z6])],[(0,[z1,z2,z1086,z3,z8,z6]),(0,[z1,z2,z1087,z5,z8,z6]),(0,[z1,z2,z26,z42,z239,z8]),(0,[z1,z2,z48,z42,z8,z72])],[(0,[z1,z2,z607,z57,z5,z6]),(0,[z24,z1,z2,z3,z5,z773]),(0,[z142,z1,z2,z276,z5,z6]),(0,[z1,z2,z3,z1088,z8,z6]),(0,[z1,z2,z812,z3,z42,z6]),(0,[z1,z2,z3,z5,z6,z953])],[(0,[z1,z410,z2,z3,z42,z8]),(0,[z1,z2,z3,z503,z42,z6]),(0,[z1,z2,z26,z5,z69,z27])],[(0,[z1,z2,z138,z5,z8,z6]),(0,[z1,z2,z3,z1089,z359,z6]),(0,[z129,z2,z3,z33,z5,z84]),(0,[z1,z2,z3,z5,z1090,z6]),(0,[z1,z2,z3,z5,z6,z1091]),(0,[z1,z2,z57,z3,z5,z1000]),(0,[z1,z2,z3,z173,z6,z27]),(0,[z1,z2,z3,z33,z6,z789])],[(0,[z1,z2,z57,z3,z254,z6]),(0,[z1,z2,z1092,z3,z5,z6]),(0,[z1,z2,z3,z1093,z8,z6]),(0,[z1,z2,z100,z33,z101,z6]),(0,[z1,z2,z1094,z3,z5,z6])],[(0,[z1,z2,z57,z212,z5,z6]),(0,[z1,z2,z3,z5,z1095,z6])],[(1,[z1,z2,z3,z42,z228]),(0,[z1,z2,z3,z1096,z8,z6])],[(0,[z1,z2,z3,z5,z1097,z6]),(0,[z1,z2,z207,z5,z272,z6]),(0,[z1,z2,z1098,z3,z5,z6]),(0,[z1,z2,z47,z3,z5,z338])],[(0,[z1,z2,z3,z5,z6,z1099]),(0,[z1,z2,z3,z432,z38,z8]),(0,[z1,z2,z57,z3,z5,z773])],[(0,[z1,z1100,z2,z3,z5,z6]),(0,[z1,z2,z1101,z3,z5,z6])],[(0,[z1,z2,z3,z5,z8,z1102]),(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z2,z100,z813,z8,z6])],[],[(0,[z137,z139,z3,z33,z5,z6]),(0,[z17,z1,z2,z3,z418,z5]),(0,[z1,z2,z3,z33,z1104,z6])],[(0,[z151,z2,z49,z8,z20,z6]),(0,[z1,z11,z3,z5,z468,z6]),(0,[z1,z2,z1105,z3,z5,z6])],[(0,[z1,z2,z1106,z3,z5,z6]),(0,[z1,z2,z26,z48,z42,z8]),(0,[z1,z2,z3,z375,z498,z27])],[(0,[z1,z2,z3,z5,z6,z1107]),(0,[z1108,z1,z2,z3,z5,z6]),(0,[z916,z11,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z91,z6]),(0,[z1,z2,z3,z5,z1109,z6]),(0,[z303,z2,z3,z5,z6,z228])],[(0,[z15,z16,z3,z5,z41,z6]),(0,[z1,z2,z3,z254,z8,z6]),(0,[z7,z151,z2,z49,z5,z6]),(0,[z1,z2,z3,z42,z41,z27]),(0,[z1,z2,z3,z5,z68,z27])],[(0,[z1,z2,z3,z5,z1110,z6])]],
   [[(0,[z1,z2,z3,z8,z1111,z6]),(0,[z1,z2,z3,z432,z5,z21]),(0,[z1,z2,z3,z432,z5,z8]),(0,[z1,z2,z47,z3,z20,z6])],[(0,[z1,z2,z3,z1112,z6,z228]),(0,[z1,z2,z3,z5,z6,z1113])],[(0,[z1,z2,z3,z5,z500,z450]),(0,[z1,z1114,z3,z5,z8,z6]),(0,[z1115,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1116,z5,z6])],[(0,[z1,z477,z51,z5,z8,z6]),(0,[z1,z2,z3,z631,z8,z20]),(0,[z1,z2,z3,z1117,z8,z6]),(0,[z350,z1,z2,z3,z5,z310]),(0,[z1,z2,z3,z120,z168,z6])],[(0,[z17,z1,z2,z3,z215,z6]),(0,[z1,z2,z1118,z3,z5,z6]),(0,[z116,z1,z2,z3,z432,z5]),(0,[z1,z2,z3,z42,z1119,z6]),(0,[z116,z1,z2,z5,z455,z6])],[],[(0,[z1,z266,z3,z5,z21,z6]),(0,[z1,z2,z3,z1120,z8,z206]),(0,[z1,z2,z1121,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1122]),(0,[z17,z1,z2,z3,z112,z6]),(0,[z17,z1,z2,z3,z42,z187]),(0,[z1,z2,z3,z1123,z20,z6])],[(0,[z1,z2,z3,z5,z1124,z6]),(0,[z43,z1,z180,z3,z5,z6]),(0,[z1,z2,z3,z1125,z5,z6]),(0,[z1,z2,z3,z1126,z20,z6])],[(0,[z1,z2,z3,z104,z461,z6])],[(0,[z1,z2,z3,z104,z8,z37]),(0,[z1,z2,z3,z1127,z5,z6]),(1,[z1,z2,z3,z42,z27])],[(0,[z1,z2,z3,z1128,z5,z6]),(0,[z1,z2,z376,z48,z5,z6])],[(0,[z1,z2,z3,z21,z20,z6]),(0,[z1,z2,z3,z8,z952,z84]),(0,[z1,z183,z2,z3,z5,z6]),(0,[z1,z11,z639,z3,z5,z6])],[(0,[z1,z2,z3,z5,z21,z1129])],[(0,[z382,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z1130,z65,z8]),(0,[z1,z2,z3,z42,z343,z8]),(0,[z1,z2,z3,z1131,z5,z6]),(0,[z1,z2,z3,z5,z1132,z6])],[(0,[z1,z2,z3,z287,z20,z6]),(0,[z1,z2,z3,z8,z1133,z6]),(0,[z1,z177,z51,z5,z563,z6])],[(0,[z1,z2,z3,z1134,z5,z6]),(0,[z1,z204,z2,z3,z418,z8])],[(0,[z1,z2,z3,z1135,z5,z8]),(0,[z1,z2,z3,z359,z464,z6]),(0,[z1,z2,z3,z5,z1136,z6]),(0,[z1,z2,z3,z20,z6,z260]),(0,[z1,z2,z3,z430,z20,z6]),(0,[z1,z2,z3,z5,z1137,z6]),(0,[z1,z2,z3,z5,z308,z27])],[],[(0,[z24,z1,z2,z3,z1138,z6]),(0,[z1,z2,z3,z5,z1139,z6]),(0,[z1,z2,z57,z3,z482,z6])],[(0,[z1,z2,z138,z114,z8,z6]),(0,[z1,z2,z3,z42,z21,z6]),(0,[z1,z2,z3,z5,z1140,z6]),(0,[z1,z2,z3,z193,z20,z6]),(0,[z1,z2,z3,z106,z482,z27])],[(0,[z1,z2,z3,z956,z8,z6]),(0,[z1,z2,z3,z42,z675,z8]),(0,[z1,z2,z3,z1141,z5,z6]),(0,[z1,z2,z3,z1104,z8,z6])],[],[(0,[z17,z1,z225,z3,z5,z6]),(0,[z1,z2,z3,z33,z5,z532]),(0,[z1,z2,z3,z1112,z6,z27])],[(0,[z1,z2,z3,z8,z1142,z6]),(0,[z1,z2,z385,z3,z42,z6]),(0,[z382,z1,z2,z5,z330,z6]),(0,[z1,z2,z3,z5,z6,z1143]),(0,[z1,z2,z3,z5,z1011,z6])],[(0,[z1,z2,z3,z8,z842,z331]),(0,[z1,z2,z3,z1144,z8,z6]),(0,[z1,z2,z3,z5,z41,z206]),(0,[z36,z116,z2,z4,z5,z6]),(0,[z1,z2,z165,z5,z40,z6]),(0,[z1,z2,z3,z5,z1145,z6])],[(0,[z1,z2,z3,z1146,z5,z6]),(0,[z1,z218,z2,z3,z42,z6]),(0,[z1,z2,z3,z5,z1147,z6]),(0,[z466,z1,z2,z3,z20,z6]),(0,[z1,z2,z57,z3,z1138,z6]),(0,[z1,z2,z3,z5,z18,z744])],[(0,[z1,z2,z3,z5,z1148,z6]),(0,[z9,z2,z3,z251,z5,z6]),(0,[z1,z2,z212,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1149]),(0,[z1,z2,z3,z823,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1150]),(0,[z1,z2,z57,z3,z498,z6]),(0,[z1,z2,z57,z222,z5,z6])],[(0,[z86,z2,z196,z3,z5,z6]),(0,[z1,z2,z3,z1151,z5,z6]),(0,[z1,z2,z3,z42,z1152,z6]),(0,[z24,z1,z2,z3,z65,z6]),(0,[z1,z56,z3,z89,z8,z6]),(0,[z1,z2,z3,z42,z1041,z6]),(0,[z1,z2,z342,z3,z432,z8]),(0,[z1,z2,z3,z42,z5,z294]),(0,[z1,z2,z3,z42,z1153,z6]),(0,[z1,z2,z3,z106,z498,z27])],[(0,[z1,z2,z3,z42,z463,z8]),(0,[z1154,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1155]),(0,[z17,z1,z2,z3,z128,z6]),(0,[z1,z2,z3,z33,z1156,z6])],[(0,[z1,z177,z51,z5,z246,z6]),(0,[z1,z2,z3,z5,z335,z27]),(0,[z1,z386,z11,z3,z5,z6]),(0,[z652,z1,z2,z57,z5,z6]),(0,[z1,z2,z3,z42,z8,z302])]],
   [[],[(0,[z1,z1157,z2,z3,z5,z6]),(0,[z1158,z1,z2,z3,z5,z6]),(0,[z1,z11,z2,z3,z281,z6]),(0,[z1,z2,z3,z42,z8,z237]),(0,[z1,z2,z341,z8,z250,z6])],[(0,[z1,z2,z3,z1159,z5,z6]),(0,[z1,z2,z3,z1160,z5,z6]),(0,[z2,z3,z359,z251,z5,z6]),(0,[z1,z3,z5,z8,z769,z70])],[(0,[z1,z2,z57,z3,z65,z6]),(0,[z1,z2,z3,z5,z8,z1161]),(0,[z1,z2,z3,z5,z8,z1162]),(0,[z1,z577,z11,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z6]),(0,[z1,z2,z207,z4,z5,z6]),(0,[z43,z916,z2,z3,z5,z6])],[(0,[z116,z1,z2,z3,z914,z6]),(0,[z1163,z1,z2,z3,z5,z6]),(0,[z340,z2,z3,z8,z367,z6])],[(0,[z1,z2,z3,z5,z8,z1164]),(0,[z1,z266,z3,z33,z5,z6]),(0,[z1,z2,z212,z4,z5,z6]),(0,[z151,z2,z57,z49,z5,z6]),(0,[z1165,z1,z2,z3,z5,z6]),(0,[z43,z1,z60,z65,z8,z6])],[(0,[z1,z11,z2,z138,z5,z6]),(0,[z1,z2,z3,z5,z8,z1166]),(0,[z1,z2,z3,z1167,z8,z6]),(0,[z1,z2,z3,z53,z637,z6])],[(0,[z1,z139,z35,z5,z8,z6]),(0,[z1168,z1,z2,z3,z5,z6]),(0,[z1169,z1,z2,z3,z5,z6]),(0,[z9,z2,z3,z5,z8,z10]),(0,[z1,z1170,z2,z3,z5,z6]),(0,[z1,z25,z3,z42,z8,z97]),(0,[z1,z2,z3,z1171,z8,z6]),(0,[z1,z2,z3,z67,z6,z27])],[(0,[z1,z2,z1172,z3,z5,z6]),(0,[z1,z2,z3,z147,z5,z228]),(0,[z1,z2,z3,z112,z8,z6]),(0,[z1,z2,z3,z1173,z5,z6]),(0,[z1,z2,z3,z20,z1174,z6]),(0,[z1,z2,z3,z308,z34,z6])],[(0,[z1,z2,z1175,z35,z5,z6]),(0,[z186,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z147,z950,z6]),(0,[z1,z2,z3,z8,z1176,z6]),(0,[z1,z2,z3,z42,z240,z8]),(0,[z1,z2,z3,z20,z6,z310]),(0,[z116,z1,z2,z165,z5,z6])],[(0,[z1,z2,z3,z114,z8,z6]),(0,[z116,z1,z2,z3,z5,z206]),(0,[z129,z2,z3,z359,z5,z84]),(0,[z1,z2,z217,z3,z482,z6])],[(0,[z1,z2,z57,z3,z343,z5]),(0,[z1,z1177,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1178,z6]),(0,[z1,z2,z47,z3,z401,z6])],[(0,[z1,z1179,z3,z5,z8,z6]),(0,[z1180,z1,z2,z3,z5,z6]),(0,[z1,z3,z5,z149,z754,z6])],[(0,[z1,z2,z3,z833,z8,z6]),(0,[z1,z2,z3,z5,z1181,z6]),(0,[z1182,z1,z2,z3,z5,z6]),(0,[z1,z191,z2,z3,z5,z74]),(0,[z1,z2,z3,z42,z630,z8])],[(0,[z16,z2,z196,z3,z5,z6]),(0,[z1,z2,z1183,z3,z5,z6]),(0,[z1,z2,z3,z42,z6,z260]),(0,[z1072,z2,z57,z3,z5,z6]),(0,[z219,z1,z2,z3,z42,z27])],[(0,[z1,z2,z3,z432,z5,z1090])],[(0,[z17,z1,z2,z3,z1184,z6]),(0,[z1,z2,z1185,z3,z5,z6])],[(0,[z1,z2,z3,z42,z8,z121]),(0,[z1,z2,z3,z8,z1186,z6])],[(0,[z1,z2,z3,z1187,z5,z6]),(0,[z1,z11,z2,z3,z254,z6]),(0,[z1,z2,z3,z462,z21,z6]),(0,[z1,z2,z3,z42,z41,z581]),(0,[z1,z2,z57,z3,z419,z6]),(0,[z1,z2,z26,z5,z294,z69]),(0,[z1,z2,z3,z42,z8,z294]),(0,[z1,z2,z3,z1188,z6,z27]),(0,[z1,z2,z3,z33,z482,z27])],[(0,[z1,z2,z3,z314,z41,z6]),(0,[z1,z2,z3,z1008,z6,z310]),(0,[z164,z1,z3,z253,z8,z6]),(0,[z1,z2,z217,z3,z498,z6])],[(1,[z1,z2,z3,z789,z27])],[(0,[z1,z2,z3,z42,z21,z10])],[(0,[z325,z139,z3,z5,z8,z6]),(0,[z17,z28,z2,z3,z92,z6]),(0,[z2,z3,z5,z243,z21,z6]),(0,[z135,z2,z3,z5,z21,z6]),(0,[z1,z11,z2,z3,z5,z773]),(0,[z1,z44,z396,z3,z42,z8])],[(0,[z1,z3,z5,z8,z97,z769]),(0,[z1,z2,z3,z5,z1189,z6]),(0,[z24,z1,z3,z242,z5,z6]),(0,[z1,z2,z3,z375,z5,z27]),(0,[z1,z2,z3,z42,z103,z18])],[(0,[z1,z2,z3,z5,z1190,z6]),(0,[z1,z2,z3,z215,z73,z6]),(0,[z1,z2,z3,z143,z5,z6]),(0,[z1,z2,z3,z20,z6,z338]),(1,[z1,z2,z3,z831,z6])],[(0,[z137,z139,z3,z5,z8,z450]),(0,[z1,z2,z3,z1191,z8,z6]),(0,[z522,z2,z3,z5,z21,z6]),(0,[z1,z2,z26,z3,z42,z27])],[(0,[z137,z139,z3,z8,z20,z6]),(0,[z1,z2,z3,z1192,z5,z6]),(0,[z1,z2,z3,z1193,z5,z6]),(0,[z1,z2,z3,z1194,z6,z228]),(0,[z1,z2,z3,z630,z5,z27])],[(0,[z1,z1195,z2,z3,z5,z6]),(0,[z17,z1,z3,z5,z149,z6]),(0,[z1,z2,z3,z1196,z5,z6]),(0,[z1,z2,z48,z217,z5,z6])],[],[(0,[z1,z2,z3,z147,z5,z27])],[(0,[z17,z1,z2,z3,z314,z6]),(0,[z1,z2,z3,z498,z21,z6]),(0,[z540,z2,z3,z5,z41,z6])]],
   [[(0,[z1,z2,z3,z1197,z20,z6]),(0,[z1,z2,z1198,z3,z5,z6])],[(0,[z1,z2,z3,z215,z8,z6]),(0,[z2,z3,z42,z252,z8,z10]),(0,[z1,z11,z3,z42,z198,z6]),(0,[z1,z25,z2,z57,z3,z42])],[(0,[z1,z2,z3,z208,z5,z41]),(0,[z17,z1,z2,z3,z106,z20]),(0,[z1,z2,z57,z5,z518,z6])],[(0,[z15,z16,z3,z5,z295,z6]),(0,[z1,z2,z3,z106,z5,z228]),(0,[z1,z2,z71,z33,z40,z6])],[(0,[z1,z2,z3,z5,z1199,z6])],[(0,[z1,z2,z165,z3,z5,z6]),(0,[z17,z1,z2,z3,z918,z6]),(0,[z1,z2,z3,z87,z5,z744]),(1,[z1,z2,z3,z462,z27])],[(0,[z1,z2,z3,z5,z288,z6]),(0,[z1,z2,z3,z1200,z8,z6]),(0,[z1,z2,z3,z1201,z5,z8]),(0,[z1,z2,z3,z5,z1202,z6]),(0,[z1,z2,z64,z57,z5,z6])],[(0,[z1,z2,z138,z5,z21,z6]),(0,[z1,z2,z3,z5,z1203,z6]),(0,[z110,z1,z218,z3,z5,z6])],[(0,[z1,z16,z180,z3,z5,z6])],[(0,[z1,z2,z3,z42,z6,z310])],[(0,[z1,z2,z3,z915,z5,z331]),(0,[z1,z2,z57,z3,z104,z6]),(0,[z1,z2,z3,z5,z1204,z6]),(0,[z1,z2,z3,z5,z1205,z6]),(0,[z1,z2,z813,z5,z8,z6]),(0,[z1,z736,z3,z5,z6,z27])],[(0,[z1,z2,z1206,z3,z5,z6])],[(0,[z1,z11,z2,z48,z3,z42])],[(0,[z1,z1207,z2,z3,z5,z6]),(0,[z1,z56,z3,z1208,z8,z6]),(0,[z17,z1,z2,z3,z401,z6]),(0,[z1,z2,z376,z5,z88,z6]),(0,[z1,z2,z3,z87,z20,z27])],[(0,[z1,z2,z3,z8,z1209,z6]),(0,[z1,z2,z3,z1210,z8,z6]),(0,[z151,z2,z49,z5,z479,z6]),(0,[z1,z2,z3,z5,z449,z27])],[(0,[z1,z3,z5,z8,z6,z1211]),(0,[z116,z9,z2,z3,z5,z10]),(0,[z172,z1,z374,z3,z5,z6])],[(0,[z1212,z1,z2,z3,z5,z6]),(0,[z1,z2,z71,z40,z6,z27]),(0,[z1,z2,z3,z42,z27,z297]),(0,[z1,z2,z3,z42,z8,z628])],[(0,[z567,z2,z3,z92,z8,z6]),(0,[z1,z2,z3,z343,z128,z8]),(0,[z1,z2,z3,z42,z193,z6]),(0,[z1,z2,z57,z395,z5,z6]),(0,[z1,z2,z3,z42,z308,z6])],[(0,[z1,z2,z3,z1213,z8,z6])],[(0,[z1,z2,z3,z1214,z8,z6]),(0,[z1,z2,z3,z5,z1215,z6]),(0,[z1,z2,z3,z5,z1216,z6]),(0,[z1,z11,z2,z3,z482,z6]),(0,[z1,z2,z3,z1217,z6,z27])],[(0,[z1,z329,z3,z42,z8,z6]),(0,[z1,z2,z3,z254,z21,z6]),(0,[z1,z25,z2,z3,z5,z310]),(0,[z1,z2,z3,z14,z419,z6]),(0,[z1,z2,z3,z20,z6,z157])],[(0,[z58,z1,z2,z3,z53,z6])],[(0,[z1,z218,z3,z5,z161,z6]),(0,[z379,z2,z3,z5,z21,z6]),(0,[z148,z66,z2,z3,z5,z6])],[(0,[z1218,z1,z2,z3,z5,z6]),(0,[z1,z847,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1219,z6]),(0,[z1220,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z359,z1156,z6]),(0,[z1,z2,z3,z288,z20,z6]),(0,[z1,z44,z11,z2,z3,z42]),(0,[z1,z2,z3,z106,z5,z27])],[(0,[z1,z2,z3,z42,z8,z195]),(0,[z131,z2,z3,z93,z21,z6]),(0,[z1,z2,z3,z289,z14,z6])],[(0,[z1,z2,z3,z1221,z8,z6]),(0,[z1,z2,z3,z1222,z5,z6]),(0,[z1,z11,z2,z3,z1138,z6]),(0,[z1,z2,z1223,z3,z5,z6]),(0,[z1,z497,z2,z3,z42,z6])],[(0,[z1,z2,z5,z21,z6,z821]),(0,[z1,z177,z905,z5,z8,z6])],[(0,[z1,z2,z1224,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1225]),(0,[z389,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z173,z8,z84]),(0,[z1,z11,z2,z3,z498,z6]),(0,[z1,z2,z3,z8,z789,z27]),(0,[z1,z2,z3,z5,z789,z27])],[(0,[z211,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1226])],[(0,[z137,z139,z3,z5,z501,z6]),(0,[z1,z2,z3,z5,z1227,z6]),(0,[z1,z2,z3,z8,z1228,z6]),(0,[z1,z2,z3,z42,z89,z27]),(0,[z1,z2,z3,z42,z8,z205])],[(0,[z1,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z1229,z6]),(0,[z1,z2,z3,z104,z6,z27]),(0,[z1,z25,z2,z3,z42,z21]),(0,[z2,z196,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z1230,z6]),(0,[z1,z2,z3,z1231,z8,z6]),(0,[z1,z2,z3,z42,z72,z27])]],
   [[(0,[z1,z2,z3,z104,z94,z6]),(0,[z1,z2,z3,z1232,z8,z6]),(0,[z1,z2,z3,z1233,z8,z6]),(0,[z166,z1,z25,z3,z5,z97])],[(0,[z1,z266,z3,z5,z461,z6]),(0,[z36,z17,z2,z4,z5,z6]),(0,[z1,z2,z1234,z3,z5,z6]),(0,[z1,z2,z3,z359,z5,z581]),(0,[z1,z2,z26,z239,z5,z8]),(0,[z1,z2,z3,z42,z1235,z6])],[(0,[z1,z857,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z1236,z6]),(0,[z1,z2,z3,z418,z5,z1017]),(0,[z1,z2,z57,z3,z67,z6]),(0,[z1,z374,z2,z3,z20,z6])],[(0,[z137,z385,z139,z3,z5,z6]),(0,[z1,z2,z3,z1237,z20,z6])],[(0,[z107,z2,z3,z5,z710,z6]),(0,[z1,z2,z3,z215,z8,z10]),(0,[z1,z11,z2,z3,z65,z6])],[(0,[z137,z17,z139,z3,z5,z6]),(0,[z1,z2,z1238,z5,z8,z6]),(0,[z110,z231,z2,z3,z5,z6]),(0,[z1,z2,z57,z5,z674,z6])],[(0,[z1,z2,z3,z42,z8,z247]),(0,[z1,z2,z3,z1239,z5,z8])],[(0,[z1,z266,z3,z8,z20,z6]),(0,[z151,z11,z2,z49,z5,z6]),(0,[z1,z2,z3,z5,z1240,z6]),(0,[z17,z1,z2,z3,z464,z6]),(0,[z1,z11,z2,z3,z5,z1063])],[(0,[z1,z2,z3,z5,z6,z1241]),(0,[z1,z2,z3,z5,z1152,z6]),(0,[z1,z2,z3,z5,z1242,z6]),(0,[z591,z1,z11,z3,z5,z6])],[(0,[z2,z3,z5,z21,z683,z6]),(0,[z1,z1243,z2,z3,z5,z6]),(0,[z1,z2,z351,z3,z75,z6])],[(0,[z1,z2,z48,z3,z173,z8])],[(0,[z1244,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1245]),(0,[z1,z2,z3,z33,z1246,z6])],[(0,[z1,z11,z2,z3,z343,z5]),(0,[z1247,z1,z2,z3,z42,z6]),(0,[z1,z2,z3,z42,z20,z27])],[(0,[z1,z2,z3,z42,z88,z27])],[(0,[z15,z1,z497,z3,z5,z6]),(0,[z1,z2,z607,z5,z8,z69])],[(0,[z1,z2,z3,z5,z8,z1248]),(0,[z1,z2,z3,z1249,z5,z6]),(0,[z1,z2,z3,z5,z1250,z6]),(0,[z1072,z11,z2,z3,z5,z6]),(0,[z1,z44,z3,z42,z8,z70]),(0,[z1,z2,z217,z3,z5,z6]),(0,[z1,z1251,z3,z42,z8,z6]),(0,[z1,z2,z3,z462,z91,z6])],[(0,[z1,z2,z3,z462,z308,z6])],[(0,[z9,z2,z3,z123,z8,z10]),(0,[z1,z2,z3,z5,z1252,z6])],[(0,[z1,z2,z3,z5,z1253,z6]),(0,[z1,z2,z3,z5,z21,z80]),(0,[z116,z1,z2,z3,z281,z6]),(0,[z1254,z2,z3,z42,z8,z6]),(0,[z1,z2,z3,z42,z6,z157])],[(0,[z1255,z1,z2,z3,z5,z6]),(0,[z1,z11,z2,z3,z419,z6]),(0,[z1,z25,z3,z5,z8,z97]),(0,[z1,z2,z3,z1256,z5,z6]),(0,[z1257,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z120,z91,z6])],[(0,[z1,z2,z3,z1258,z5,z6]),(0,[z1,z2,z3,z173,z656,z6])],[(0,[z1,z2,z3,z5,z1259,z6]),(0,[z9,z2,z57,z3,z5,z10]),(0,[z1,z2,z71,z361,z40,z6])],[(0,[z1,z1260,z2,z3,z5,z6]),(0,[z1,z25,z2,z3,z1261,z8])],[(0,[z1,z2,z3,z521,z6,z228]),(0,[z1,z2,z3,z5,z1262,z6]),(0,[z1,z2,z3,z14,z5,z6])],[(0,[z116,z1,z2,z138,z5,z6]),(0,[z1263,z1,z2,z3,z5,z6]),(0,[z1264,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z277,z6]),(0,[z1,z2,z3,z5,z18,z411])],[(0,[z1,z2,z1265,z5,z8,z6]),(0,[z1,z2,z3,z42,z8,z366]),(0,[z1,z2,z3,z1266,z8,z6]),(0,[z2,z3,z251,z5,z41,z6]),(0,[z1,z2,z3,z45,z20,z6])],[(0,[z1,z403,z3,z5,z8,z97]),(0,[z1,z2,z3,z5,z6,z260]),(0,[z1,z2,z3,z728,z6,z27])],[(0,[z1267,z1,z2,z138,z5,z6]),(0,[z116,z1,z2,z3,z289,z6]),(0,[z1,z2,z3,z5,z237,z27]),(0,[z1268,z1,z2,z3,z5,z6])],[(0,[z1,z56,z2,z3,z418,z8]),(0,[z17,z1,z3,z5,z345,z6]),(0,[z1,z2,z5,z8,z1269,z69])],[(0,[z9,z2,z3,z5,z21,z10]),(0,[z1,z2,z57,z5,z122,z6]),(0,[z1,z2,z3,z5,z8,z1270]),(0,[z17,z1,z2,z3,z827,z5]),(0,[z1,z2,z100,z101,z337,z6]),(0,[z1,z2,z3,z42,z106,z27]),(0,[z1,z2,z3,z1184,z6,z27])],[(0,[z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z112,z21,z6]),(0,[z129,z1,z2,z3,z42,z27]),(0,[z124,z1,z2,z3,z427,z6]),(0,[z58,z1,z2,z3,z327,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z1271]),(0,[z1,z11,z329,z3,z5,z6]),(0,[z151,z2,z152,z49,z5,z6]),(0,[z107,z1,z2,z3,z42,z27]),(0,[z1,z2,z3,z1089,z8,z6]),(0,[z1,z11,z3,z242,z5,z6])],[(0,[z1,z2,z3,z114,z21,z6]),(0,[z1,z2,z3,z1272,z5,z6]),(0,[z1,z2,z3,z147,z5,z84]),(0,[z1,z2,z3,z33,z5,z301]),(0,[z1,z2,z3,z5,z1273,z6]),(0,[z1274,z1,z2,z3,z5,z6])],[(0,[z443,z1,z2,z3,z42,z6]),(1,[z916,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z33,z18]),(0,[z166,z1,z2,z3,z482,z6])],[(0,[z116,z1,z2,z207,z5,z6]),(0,[z1,z2,z3,z1275,z6,z581]),(0,[z116,z1,z25,z3,z5,z97])],[(0,[z137,z139,z3,z5,z500,z6]),(0,[z1,z2,z508,z101,z8,z6]),(0,[z1,z2,z3,z5,z8,z1276]),(0,[z1,z2,z3,z42,z344,z6]),(0,[z1,z2,z3,z42,z5,z157])],[(0,[z116,z1,z2,z3,z254,z6]),(0,[z1,z2,z1277,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1278]),(0,[z775,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1279,z5,z8]),(0,[z1,z2,z3,z106,z8,z20])],[(0,[z1,z2,z3,z5,z10,z411])],[(0,[z1,z2,z3,z5,z1280,z6])],[(0,[z1,z2,z3,z1281,z8,z6]),(0,[z116,z1,z2,z601,z5,z6])],[(0,[z1,z2,z3,z1282,z5,z6]),(0,[z1,z2,z3,z5,z1283,z6])],[(0,[z1,z11,z2,z3,z104,z6]),(0,[z1,z2,z3,z42,z8,z284]),(0,[z1,z2,z3,z42,z41,z6]),(0,[z1,z2,z3,z8,z1217,z6]),(0,[z166,z1,z2,z3,z498,z6])],[],[(0,[z1,z2,z3,z521,z6,z27]),(0,[z1,z1284,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1285,z6]),(0,[z2,z3,z5,z392,z21,z6]),(0,[z1,z516,z3,z89,z8,z6]),(0,[z166,z17,z1,z2,z3,z42]),(0,[z1,z2,z3,z5,z1286,z6]),(0,[z1,z2,z3,z42,z1287,z6]),(0,[z1,z2,z758,z5,z6,z27])],[(0,[z1,z2,z3,z1288,z5,z6])],[(0,[z1,z2,z3,z1289,z5,z6]),(0,[z1290,z1,z2,z3,z5,z6]),(0,[z1,z2,z1291,z3,z5,z6])],[(0,[z1,z2,z3,z91,z41,z6])],[(0,[z116,z1,z2,z57,z5,z6])],[(0,[z1,z2,z3,z33,z5,z80]),(0,[z1,z2,z3,z5,z1292,z6]),(0,[z1,z2,z3,z8,z237,z20])],[(0,[z443,z1,z3,z5,z203,z6]),(0,[z1,z44,z3,z42,z253,z8]),(0,[z1,z2,z3,z42,z1293,z6])],[(0,[z1,z329,z3,z254,z8,z6]),(0,[z1,z2,z3,z5,z6,z310]),(0,[z1,z2,z57,z3,z42,z27]),(0,[z1,z2,z3,z20,z6,z411])],[(0,[z1,z2,z3,z1294,z281,z6]),(0,[z1,z2,z3,z20,z1295,z6])],[(0,[z1,z2,z3,z8,z1296,z6]),(0,[z1,z1297,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1298]),(0,[z1,z44,z2,z3,z42,z103]),(0,[z1,z2,z3,z120,z6,z157])],[(0,[z1,z2,z3,z1299,z8,z6]),(0,[z1,z2,z3,z1300,z5,z6]),(0,[z1,z2,z3,z344,z419,z6]),(0,[z90,z1,z2,z3,z5,z411]),(0,[z1,z2,z258,z3,z42,z8])],[(0,[z1,z2,z3,z42,z362,z6]),(0,[z1,z1301,z3,z42,z8,z6])],[(0,[z1,z2,z35,z5,z41,z6]),(0,[z1,z231,z2,z3,z5,z6]),(0,[z1,z2,z1302,z3,z5,z6]),(0,[z1,z177,z51,z5,z8,z6])],[(0,[z1,z2,z3,z42,z334,z6]),(0,[z1,z2,z57,z42,z115,z6]),(0,[z1,z2,z3,z42,z8,z157]),(0,[z1,z2,z3,z776,z6,z27])],[(0,[z1,z2,z3,z5,z1303,z6]),(0,[z1,z11,z2,z878,z5,z6])],[(0,[z1,z16,z35,z5,z8,z6]),(0,[z328,z2,z3,z5,z8,z84]),(0,[z1,z2,z26,z57,z3,z42]),(0,[z1,z2,z3,z42,z430,z6])],[(0,[z1,z2,z3,z5,z8,z1304]),(0,[z1305,z1,z2,z3,z5,z6]),(0,[z116,z1,z2,z48,z3,z42])],[(0,[z107,z2,z3,z503,z5,z6]),(0,[z1,z2,z3,z1306,z8,z6]),(0,[z1,z2,z3,z59,z5,z68])]],
   [[(0,[z1,z2,z3,z1156,z8,z6]),(0,[z1,z2,z3,z1307,z5,z6])],[(0,[z1308,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1309,z6])],[(0,[z1,z2,z3,z469,z5,z27]),(0,[z1,z2,z3,z42,z103,z27]),(0,[z1,z2,z3,z462,z33,z18])],[(0,[z1,z2,z3,z1310,z8,z6]),(0,[z1,z2,z3,z65,z41,z6]),(0,[z1,z11,z2,z3,z67,z6]),(0,[z1,z2,z3,z462,z8,z18])],[(0,[z1,z2,z3,z1311,z8,z6]),(0,[z131,z2,z3,z33,z93,z6]),(0,[z1,z2,z3,z5,z1312,z6]),(0,[z1,z2,z3,z5,z6,z338]),(0,[z219,z1,z2,z3,z42,z5])],[(0,[z1,z2,z3,z79,z42,z6]),(0,[z116,z1,z2,z3,z482,z6]),(0,[z1,z2,z3,z173,z488,z6])],[(0,[z1,z2,z3,z173,z8,z6]),(0,[z1,z2,z270,z3,z5,z338])],[(0,[z1,z2,z3,z5,z1313,z6]),(0,[z1,z2,z3,z1314,z5,z6]),(0,[z1,z2,z3,z5,z6,z1315]),(0,[z116,z1,z56,z3,z89,z6])],[(0,[z1,z2,z35,z5,z8,z331]),(0,[z1,z177,z57,z51,z5,z6])],[(0,[z1,z2,z3,z123,z21,z6]),(0,[z2,z3,z5,z355,z41,z6])],[(0,[z1,z2,z3,z1316,z8,z6]),(0,[z1317,z1,z2,z3,z5,z6]),(0,[z1,z56,z3,z423,z89,z6]),(0,[z116,z1,z44,z2,z3,z42])],[(0,[z1,z2,z57,z35,z5,z6]),(0,[z1,z2,z3,z462,z41,z6])],[(0,[z1,z56,z3,z343,z89,z8]),(0,[z1,z2,z3,z5,z1318,z6]),(0,[z1,z2,z57,z3,z42,z20])],[(0,[z1,z2,z3,z5,z1235,z6]),(0,[z1,z2,z3,z5,z971,z6]),(0,[z1,z2,z341,z40,z8,z6])],[(0,[z142,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z1319,z5,z6]),(0,[z116,z1,z2,z3,z498,z6]),(0,[z1,z2,z3,z42,z239,z27]),(0,[z1,z2,z217,z3,z42,z27])],[],[],[(0,[z1,z2,z152,z3,z5,z6]),(0,[z1,z2,z3,z94,z20,z6]),(0,[z1,z2,z3,z5,z6,z1320])],[(0,[z1321,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z521,z359,z6]),(0,[z99,z1,z2,z3,z343,z5]),(0,[z1,z2,z3,z5,z1322,z6])],[(0,[z1,z1323,z2,z3,z5,z6]),(0,[z1,z1324,z2,z3,z5,z6]),(0,[z1,z2,z3,z1325,z5,z6]),(0,[z1,z2,z3,z42,z6,z411])],[(0,[z1,z2,z3,z21,z482,z6]),(0,[z1,z2,z3,z42,z308,z237])],[(0,[z1,z2,z3,z5,z8,z1326]),(0,[z1,z2,z1327,z3,z5,z6]),(0,[z116,z1,z2,z3,z65,z6]),(0,[z1,z2,z3,z20,z6,z789])],[(0,[z9,z11,z2,z3,z5,z10]),(0,[z1328,z1,z2,z3,z65,z6]),(0,[z142,z43,z1,z60,z5,z6]),(0,[z1,z2,z3,z5,z1329,z6]),(0,[z1,z2,z3,z42,z227,z6])],[(0,[z1,z2,z1330,z3,z5,z6]),(0,[z1,z307,z3,z89,z8,z6]),(0,[z1,z2,z3,z8,z20,z1023])],[(0,[z1,z266,z3,z5,z94,z6]),(0,[z1,z2,z3,z5,z1331,z6]),(0,[z1,z2,z3,z359,z5,z6]),(0,[z1,z847,z3,z5,z6,z228]),(0,[z1,z2,z3,z1332,z401,z6])],[(0,[z1,z2,z3,z5,z461,z6]),(0,[z1,z2,z3,z1015,z8,z6]),(0,[z1,z2,z758,z3,z5,z6]),(0,[z1,z497,z3,z5,z6,z96])],[(0,[z1,z266,z3,z104,z8,z6]),(0,[z1333,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1119,z5,z6]),(0,[z1,z2,z3,z42,z27,z456]),(0,[z1,z183,z3,z155,z5,z6])],[(0,[z1,z2,z3,z5,z1334,z6]),(0,[z1,z2,z3,z1335,z5,z6]),(0,[z1,z2,z3,z1336,z5,z6]),(0,[z1,z2,z3,z5,z70,z338]),(0,[z1,z1251,z3,z5,z8,z6])],[],[(0,[z1,z1337,z329,z3,z5,z6]),(0,[z1,z2,z3,z1338,z5,z6]),(0,[z90,z1,z2,z3,z42,z8]),(0,[z1,z2,z3,z1339,z5,z6]),(0,[z1,z2,z3,z498,z6,z456])],[(0,[z1,z2,z138,z5,z41,z6]),(0,[z1,z2,z3,z5,z1340,z6]),(0,[z1,z2,z57,z3,z42,z10]),(0,[z1254,z2,z3,z5,z8,z6]),(0,[z116,z1,z2,z3,z343,z5]),(0,[z1,z11,z3,z274,z5,z6]),(0,[z219,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z5,z1341,z6])]],
   [[(0,[z1,z2,z3,z8,z20,z6]),(0,[z2,z3,z1342,z92,z8,z6]),(0,[z1,z2,z1343,z3,z5,z6])],[(0,[z1,z1344,z2,z3,z20,z6])],[(0,[z1,z2,z3,z42,z8,z378]),(0,[z1,z2,z3,z343,z5,z27]),(0,[z1,z25,z57,z3,z5,z97])],[(0,[z1,z2,z3,z5,z21,z237]),(0,[z1,z2,z3,z521,z961,z6]),(0,[z1345,z1,z2,z3,z5,z6])],[(0,[z116,z151,z2,z49,z5,z6])],[(0,[z1,z2,z3,z33,z123,z6]),(0,[z1,z2,z1346,z3,z5,z6])],[(0,[z116,z1,z2,z3,z419,z6])],[(0,[z1,z2,z3,z42,z479,z6]),(0,[z1,z2,z3,z337,z20,z6])],[(0,[z1,z2,z35,z33,z5,z6]),(0,[z1,z2,z3,z5,z1347,z6])],[(0,[z1,z2,z3,z1064,z5,z6])],[(0,[z1,z2,z3,z5,z1348,z6]),(0,[z1,z25,z3,z5,z21,z97]),(0,[z1,z2,z3,z1349,z5,z8])],[(0,[z1350,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z1351,z6,z338]),(0,[z1,z2,z3,z1352,z5,z6]),(0,[z1,z2,z3,z42,z53,z27])],[(0,[z1,z2,z3,z254,z41,z6]),(0,[z1,z2,z1353,z3,z5,z6])],[(0,[z36,z0,z2,z4,z5,z6]),(0,[z1,z2,z3,z1354,z5,z6]),(0,[z1,z2,z1355,z3,z5,z6])],[(0,[z1,z847,z3,z5,z6,z27])],[(0,[z1,z218,z139,z3,z5,z6]),(0,[z1,z3,z5,z6,z1211,z228]),(0,[z1,z2,z3,z5,z8,z1356]),(0,[z116,z1,z1357,z3,z5,z6])],[(0,[z1,z2,z3,z42,z295,z6]),(0,[z1,z2,z3,z5,z1358,z6]),(0,[z1,z2,z1359,z3,z5,z6]),(0,[z1,z2,z3,z469,z8,z20]),(0,[z2,z3,z41,z21,z20,z6]),(0,[z43,z1,z60,z33,z5,z6]),(0,[z17,z1,z2,z1087,z5,z6]),(0,[z1,z2,z57,z3,z42,z413]),(0,[z1,z2,z3,z42,z1360,z6])],[(1,[z2,z742,z5,z8,z6]),(0,[z1361,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z8,z326]),(0,[z17,z1,z25,z2,z3,z42])],[(0,[z1,z2,z3,z1362,z8,z6]),(0,[z116,z1,z329,z3,z5,z6]),(0,[z148,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z42,z10,z27]),(0,[z1,z2,z3,z42,z1363,z6]),(0,[z1,z2,z3,z5,z6,z1364]),(0,[z1,z2,z3,z42,z8,z68])],[(0,[z1,z2,z3,z1365,z5,z6]),(0,[z1,z191,z2,z3,z462,z6])],[(0,[z1,z2,z3,z5,z1366,z6]),(0,[z1,z2,z3,z1367,z5,z6]),(0,[z1,z2,z3,z8,z20,z80]),(0,[z1,z2,z3,z5,z6,z1368]),(0,[z1,z497,z2,z3,z42,z8]),(0,[z1,z2,z3,z106,z20,z157])],[(0,[z1,z2,z3,z42,z8,z311]),(0,[z1,z2,z3,z42,z1369,z6])],[(0,[z1,z2,z3,z21,z419,z6]),(0,[z1,z11,z2,z3,z42,z27]),(0,[z1,z183,z2,z3,z42,z6])],[(0,[z1,z2,z1370,z3,z5,z6])],[(0,[z1,z2,z152,z5,z122,z6]),(0,[z1,z2,z3,z5,z1371,z6]),(0,[z1,z2,z57,z3,z42,z84]),(0,[z1,z2,z3,z8,z1372,z6]),(0,[z1373,z2,z3,z42,z8,z6])],[(0,[z1,z2,z5,z771,z115,z6])],[(0,[z1,z2,z3,z33,z343,z5])],[(0,[z1,z2,z3,z5,z84,z581]),(0,[z1,z44,z2,z3,z42,z45])],[(0,[z448,z1,z2,z3,z264,z6]),(0,[z1,z497,z2,z3,z106,z5])],[(0,[z116,z1,z2,z3,z104,z6]),(0,[z1,z2,z3,z8,z1374,z6]),(0,[z1,z2,z3,z174,z8,z6])],[(0,[z1,z2,z3,z5,z6,z1375]),(0,[z1,z2,z3,z42,z34,z27])],[(0,[z1,z2,z3,z5,z50,z6]),(0,[z1,z2,z3,z42,z418,z8])]],
   [[(0,[z1376,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z831,z20,z6])],[(0,[z1,z2,z3,z5,z1377,z6]),(0,[z15,z16,z3,z5,z377,z6]),(0,[z1,z2,z3,z1378,z5,z6]),(0,[z1,z2,z3,z33,z5,z74])],[(0,[z1,z2,z3,z29,z20,z6]),(0,[z1,z2,z3,z5,z6,z1379]),(0,[z1,z374,z3,z5,z89,z6])],[(0,[z1,z2,z3,z5,z501,z6]),(0,[z1,z497,z2,z3,z20,z6])],[(0,[z36,z2,z742,z5,z8,z6]),(0,[z1,z2,z3,z5,z6,z1380]),(0,[z17,z1,z2,z3,z42,z18]),(0,[z1,z3,z5,z6,z1211,z27])],[(0,[z17,z1,z266,z3,z5,z6]),(0,[z1,z2,z3,z8,z1381,z37]),(0,[z1,z2,z212,z3,z42,z6]),(0,[z1,z2,z3,z42,z436,z6]),(0,[z1,z2,z3,z42,z120,z6])],[(0,[z1,z2,z3,z482,z6,z27])],[(0,[z1382,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1383,z5,z6])],[(0,[z1,z2,z3,z5,z8,z936]),(0,[z1,z2,z3,z1046,z8,z6]),(0,[z1,z2,z3,z432,z5,z361]),(0,[z1,z2,z3,z5,z430,z6])],[(0,[z1,z2,z3,z950,z8,z6]),(0,[z1,z56,z3,z89,z41,z6]),(0,[z24,z1,z180,z3,z5,z6])],[(0,[z36,z66,z2,z3,z5,z6]),(0,[z28,z1,z2,z3,z42,z27]),(0,[z1328,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z128,z8]),(0,[z1,z2,z3,z42,z8,z481]),(0,[z219,z1,z2,z3,z401,z6])],[(0,[z1,z11,z2,z35,z5,z6]),(0,[z129,z2,z3,z42,z8,z84]),(0,[z1,z180,z2,z3,z42,z6]),(0,[z1,z2,z3,z251,z20,z6])],[(0,[z1,z2,z3,z1384,z5,z6]),(0,[z1,z11,z2,z3,z42,z20]),(0,[z1,z2,z3,z42,z743,z6])],[(0,[z1,z329,z57,z3,z5,z6]),(0,[z1,z2,z3,z1385,z5,z37]),(0,[z1,z2,z3,z1386,z8,z6]),(0,[z1,z497,z177,z3,z5,z6])],[(0,[z1,z2,z47,z3,z5,z6]),(0,[z1,z2,z26,z3,z42,z430])],[(0,[z1,z2,z3,z1387,z5,z6]),(0,[z1,z2,z3,z5,z6,z1388]),(0,[z1,z177,z51,z5,z21,z6]),(0,[z1,z2,z3,z343,z8,z20]),(0,[z1,z2,z3,z1389,z5,z6])],[],[(0,[z1,z2,z26,z5,z41,z69]),(0,[z1,z2,z3,z50,z20,z6]),(0,[z9,z2,z3,z300,z5,z10]),(0,[z1,z2,z3,z1390,z5,z6]),(0,[z7,z437,z2,z3,z5,z6]),(0,[z1,z2,z3,z1391,z59,z6]),(0,[z1,z2,z3,z5,z1392,z6])],[(0,[z1,z1393,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z92,z27]),(0,[z1,z2,z3,z1394,z8,z6])],[],[(0,[z116,z1,z2,z3,z67,z6])],[(0,[z1,z2,z3,z1395,z5,z6]),(0,[z1,z329,z3,z5,z21,z6]),(0,[z9,z2,z3,z5,z41,z10]),(0,[z1,z2,z3,z240,z5,z27]),(0,[z1,z2,z3,z5,z8,z1396]),(0,[z1,z2,z3,z1126,z5,z6])],[(0,[z1,z2,z3,z112,z41,z6]),(0,[z1,z2,z3,z5,z1397,z6]),(0,[z1,z2,z3,z5,z6,z1398]),(0,[z1,z1399,z2,z3,z5,z6]),(0,[z1,z2,z376,z57,z5,z6]),(0,[z1,z2,z3,z87,z482,z27])],[(0,[z1,z25,z11,z2,z3,z42])],[(0,[z1,z2,z3,z114,z41,z6]),(0,[z1,z2,z3,z1400,z5,z8]),(0,[z1,z2,z439,z3,z42,z8]),(0,[z1,z722,z48,z3,z5,z6]),(0,[z1,z2,z3,z42,z251,z6])],[(0,[z1,z2,z3,z73,z20,z6]),(0,[z1,z2,z3,z1401,z8,z6]),(0,[z1,z2,z3,z5,z1402,z6]),(0,[z1,z2,z71,z813,z8,z6]),(0,[z415,z1,z2,z3,z42,z8]),(1,[z1,z2,z3,z6,z789])],[(0,[z1,z2,z3,z5,z1403,z6]),(0,[z1,z44,z2,z3,z42,z27]),(0,[z219,z1,z2,z3,z776,z6]),(0,[z1,z2,z5,z8,z6,z1269])],[(0,[z382,z1,z2,z3,z5,z6]),(0,[z1404,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z173,z21,z6]),(0,[z1,z2,z3,z5,z1405,z6]),(0,[z1,z11,z2,z3,z5,z237]),(0,[z1,z2,z3,z1392,z20,z6]),(0,[z1,z191,z2,z3,z91,z6])],[(0,[z1,z2,z3,z1406,z5,z6]),(1,[z1,z2,z858,z5,z6]),(0,[z1,z2,z5,z6,z821,z27])],[(0,[z1,z2,z3,z158,z20,z6]),(0,[z1,z2,z57,z3,z418,z5]),(0,[z1,z2,z3,z20,z6,z557])],[(0,[z1,z2,z3,z5,z1407,z6])]],
   [[(0,[z1408,z1,z2,z3,z5,z6]),(0,[z1,z2,z217,z5,z115,z6]),(0,[z1,z2,z3,z87,z498,z27])],[(0,[z562,z2,z3,z93,z8,z6]),(0,[z1,z2,z1409,z3,z5,z6]),(0,[z1,z2,z3,z5,z1295,z6]),(0,[z17,z1,z2,z3,z173,z6]),(0,[z1,z2,z57,z3,z91,z6]),(0,[z257,z1,z2,z3,z42,z27])],[(0,[z2,z3,z5,z8,z6,z788]),(0,[z1,z2,z3,z5,z8,z1410]),(0,[z1,z2,z3,z193,z5,z6])],[(0,[z1,z2,z3,z1275,z8,z6])],[(0,[z1,z2,z3,z42,z169,z6]),(0,[z1,z2,z3,z143,z42,z6])],[(0,[z1,z2,z3,z21,z67,z6]),(0,[z1,z191,z2,z3,z112,z6]),(0,[z1,z2,z71,z40,z8,z6]),(0,[z166,z1,z2,z3,z42,z27])],[(0,[z1,z2,z3,z5,z6,z1411]),(0,[z445,z2,z3,z5,z8,z10])],[(0,[z24,z916,z2,z3,z5,z6]),(0,[z1,z2,z3,z554,z20,z6]),(0,[z1,z11,z3,z198,z20,z6]),(0,[z1412,z1,z2,z3,z5,z6])],[(0,[z1,z2,z35,z5,z8,z450]),(0,[z382,z1,z2,z4,z5,z6]),(0,[z466,z1,z2,z3,z5,z6]),(0,[z116,z1,z2,z3,z5,z1166])],[(0,[z1,z2,z3,z5,z500,z6]),(0,[z1,z2,z3,z1413,z8,z6]),(0,[z1,z2,z3,z5,z80,z1414]),(0,[z1,z2,z3,z33,z208,z5]),(0,[z1,z1415,z2,z3,z5,z6]),(0,[z600,z1,z2,z3,z42,z27])],[(0,[z1,z2,z3,z725,z5,z8]),(0,[z1,z2,z57,z3,z112,z6]),(0,[z1,z2,z57,z3,z42,z187])],[(0,[z443,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z1416,z8,z6]),(0,[z1,z2,z3,z42,z997,z8])],[(0,[z1,z1417,z2,z3,z5,z6]),(0,[z452,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z42,z444,z6]),(1,[z1,z2,z3,z42,z294]),(0,[z1,z2,z3,z462,z33,z27])],[(0,[z610,z1,z60,z5,z8,z6]),(0,[z131,z2,z3,z8,z367,z6]),(0,[z1,z2,z3,z5,z1418,z6]),(0,[z1,z11,z2,z3,z5,z1270]),(0,[z1,z1419,z2,z3,z5,z6])],[(0,[z1,z56,z3,z418,z89,z8])],[(0,[z1,z2,z3,z5,z8,z1420]),(0,[z1,z2,z3,z215,z41,z6])],[(0,[z1,z2,z5,z8,z6,z821]),(0,[z1,z374,z51,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1421,z6]),(0,[z1,z847,z3,z5,z6,z84]),(0,[z1,z2,z3,z1422,z8,z6]),(0,[z1,z2,z3,z42,z8,z532])],[(0,[z1,z2,z3,z5,z94,z6]),(0,[z1,z44,z3,z5,z21,z70]),(0,[z491,z231,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z479,z6]),(0,[z1,z2,z3,z5,z1423,z6]),(0,[z1,z2,z3,z1424,z5,z8]),(0,[z1,z1425,z2,z3,z5,z6]),(0,[z1,z2,z3,z837,z8,z6]),(0,[z1,z2,z3,z59,z103,z6])],[(0,[z1,z2,z3,z104,z8,z6]),(0,[z2,z3,z5,z6,z557,z228]),(0,[z1,z2,z3,z5,z72,z74])],[(0,[z1426,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z480])],[(0,[z1,z191,z2,z3,z5,z12])],[(0,[z1,z2,z3,z1427,z5,z6]),(0,[z1,z2,z3,z20,z6,z228]),(0,[z1,z2,z3,z20,z6,z505]),(0,[z1,z191,z2,z3,z956,z6]),(0,[z1,z2,z3,z42,z482,z27])],[(0,[z1,z2,z858,z5,z6,z27])],[(0,[z186,z1,z2,z3,z5,z6]),(0,[z36,z2,z4,z5,z41,z6]),(0,[z1,z11,z2,z3,z42,z84]),(0,[z1,z2,z3,z5,z1428,z6])],[(0,[z1,z2,z3,z42,z8,z538]),(0,[z17,z1,z2,z3,z1117,z6]),(0,[z1290,z1,z2,z3,z208,z5]),(0,[z1,z2,z3,z42,z401,z8])],[(0,[z110,z1,z2,z3,z42,z6]),(0,[z1,z2,z3,z33,z5,z195]),(0,[z1,z2,z26,z3,z5,z411])],[(0,[z1,z2,z3,z5,z295,z6]),(0,[z1,z2,z57,z582,z5,z6])],[(0,[z303,z2,z3,z5,z21,z6]),(0,[z1,z2,z51,z3,z42,z27]),(0,[z1,z2,z3,z5,z645,z27]),(0,[z1,z11,z2,z71,z40,z6]),(0,[z1,z2,z3,z42,z6,z557])],[(0,[z1,z2,z1429,z3,z5,z6]),(0,[z24,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z5,z1430,z6]),(0,[z1,z2,z3,z5,z8,z1431]),(0,[z1,z2,z3,z5,z1432,z6]),(0,[z1,z2,z48,z3,z5,z411]),(0,[z1,z2,z3,z42,z1433,z6])],[(0,[z1,z516,z3,z8,z370,z6])]],
   [[(0,[z738,z139,z3,z5,z8,z6]),(0,[z1,z2,z787,z5,z8,z6]),(0,[z1,z191,z2,z3,z20,z6]),(0,[z1,z2,z26,z33,z5,z69]),(0,[z1,z2,z3,z33,z5,z205]),(0,[z1,z2,z3,z42,z498,z27])],[(0,[z1,z2,z3,z5,z8,z1434]),(0,[z1,z2,z3,z5,z6,z789]),(0,[z1,z1435,z2,z3,z5,z6])],[(0,[z1,z2,z3,z106,z8,z464]),(0,[z1,z2,z57,z3,z128,z6]),(0,[z1,z2,z3,z33,z91,z27])],[(0,[z1,z2,z3,z1436,z8,z6]),(0,[z1,z2,z3,z1437,z8,z6]),(0,[z99,z1,z2,z3,z42,z6]),(0,[z1,z2,z85,z101,z8,z6]),(0,[z1,z2,z196,z3,z20,z6]),(0,[z1,z2,z3,z1438,z112,z6]),(0,[z1,z2,z217,z3,z42,z5])],[(0,[z1,z2,z3,z5,z1439,z6]),(0,[z1440,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z418,z5,z27]),(0,[z1,z1357,z3,z5,z8,z6]),(0,[z1373,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z1441,z8,z6]),(0,[z1442,z1,z2,z3,z20,z6]),(0,[z58,z1,z2,z3,z42,z27]),(0,[z1,z2,z3,z1443,z5,z6])],[(0,[z1,z2,z57,z3,z20,z6])],[(0,[z704,z2,z49,z5,z8,z6]),(0,[z2,z3,z503,z5,z41,z6]),(0,[z1,z2,z3,z42,z828,z6])],[(0,[z15,z16,z3,z42,z8,z6]),(0,[z1,z2,z3,z42,z359,z84]),(0,[z24,z43,z1,z60,z5,z6])],[(0,[z1,z1444,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z289,z6]),(0,[z116,z1,z2,z3,z42,z27]),(0,[z1,z2,z3,z5,z6,z1445])],[(0,[z1,z2,z905,z5,z8,z6]),(0,[z1,z66,z2,z3,z20,z6])],[(0,[z1,z2,z1446,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z1447]),(0,[z1,z2,z3,z5,z8,z1034]),(0,[z17,z1,z2,z3,z521,z6])],[(0,[z1,z2,z48,z3,z42,z41]),(0,[z1,z2,z1448,z3,z5,z6]),(0,[z1,z2,z1449,z5,z8,z6]),(0,[z1,z44,z3,z14,z5,z70]),(0,[z1,z25,z3,z8,z20,z97])],[(0,[z1,z2,z3,z5,z1450,z6]),(0,[z1,z2,z3,z1451,z5,z6]),(0,[z219,z116,z1,z2,z3,z42])],[(0,[z1,z2,z3,z5,z41,z331])],[(0,[z1,z2,z3,z79,z20,z6])],[(0,[z1,z2,z3,z1197,z5,z6]),(0,[z1,z2,z3,z42,z103,z6])],[(0,[z1,z11,z61,z3,z5,z6])],[(0,[z137,z2,z196,z3,z5,z6]),(0,[z7,z66,z2,z3,z5,z6]),(0,[z1452,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z831,z6,z27])],[(0,[z0,z1,z2,z3,z42,z6]),(0,[z1,z11,z180,z3,z5,z6]),(0,[z17,z1,z2,z1453,z5,z6]),(0,[z117,z2,z3,z503,z5,z6])],[(0,[z1,z2,z3,z5,z1454,z6]),(0,[z58,z1,z2,z3,z202,z6]),(0,[z1,z1455,z2,z3,z5,z6]),(0,[z43,z1,z905,z5,z8,z6]),(0,[z1,z2,z3,z1184,z8,z6])],[(0,[z36,z11,z2,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1456]),(0,[z1,z2,z3,z5,z8,z1457])],[(0,[z1,z2,z1458,z3,z5,z6]),(0,[z1,z2,z3,z8,z1188,z6])],[(0,[z1,z2,z3,z42,z6,z228]),(0,[z1,z2,z3,z42,z6,z505]),(0,[z1459,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z59,z321,z6])],[(0,[z66,z2,z49,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1460]),(0,[z269,z1,z2,z3,z327,z6]),(0,[z1,z25,z2,z3,z42,z103])],[(0,[z1,z2,z3,z5,z1461,z6]),(0,[z1462,z1,z2,z3,z5,z6]),(0,[z1,z1463,z2,z3,z5,z6]),(0,[z129,z2,z3,z5,z8,z84])],[(0,[z1,z2,z3,z5,z6,z1464]),(0,[z1,z2,z1465,z3,z5,z6])],[(0,[z151,z2,z196,z3,z5,z6]),(0,[z1,z2,z3,z5,z1466,z6]),(0,[z1,z2,z3,z5,z563,z6]),(0,[z1,z2,z3,z5,z8,z1467]),(0,[z90,z116,z1,z2,z3,z42])],[(0,[z1,z2,z217,z3,z42,z6])],[(0,[z1,z1468,z2,z3,z5,z6]),(0,[z1,z11,z529,z3,z5,z6]),(0,[z1,z2,z3,z432,z5,z27]),(0,[z1,z2,z3,z87,z5,z27])],[(0,[z1,z2,z1469,z5,z8,z6]),(0,[z1,z2,z3,z5,z1470,z6]),(0,[z1,z2,z26,z3,z42,z294]),(0,[z1,z2,z1471,z3,z5,z6])],[(0,[z116,z1,z2,z35,z5,z6]),(0,[z1,z2,z3,z1472,z8,z6]),(0,[z1,z2,z3,z33,z5,z744])],[(0,[z1,z11,z2,z3,z418,z5]),(0,[z1,z11,z2,z3,z42,z74]),(0,[z116,z1,z2,z3,z42,z20])]],
   [[],[(0,[z137,z139,z3,z5,z8,z6]),(0,[z1,z2,z3,z42,z8,z206]),(0,[z1,z2,z3,z6,z789,z27]),(0,[z1,z2,z3,z5,z6,z1473])],[(0,[z1474,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z521,z8,z6]),(0,[z1,z25,z3,z5,z41,z97]),(0,[z1,z2,z3,z5,z6,z1475]),(0,[z1,z11,z2,z3,z91,z6])],[(0,[z1,z2,z3,z1476,z5,z8]),(0,[z1,z1477,z2,z3,z5,z6]),(0,[z1,z2,z3,z343,z5,z21]),(0,[z1478,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z208,z5,z361]),(0,[z1,z2,z48,z3,z42,z8])],[(0,[z1,z2,z774,z5,z8,z6]),(0,[z1,z2,z3,z1479,z5,z6]),(0,[z1,z2,z207,z49,z5,z6]),(0,[z1,z2,z3,z5,z6,z1480]),(0,[z43,z1,z60,z281,z8,z6]),(0,[z1,z2,z3,z42,z8,z557])],[(0,[z110,z15,z16,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z581]),(0,[z1,z2,z57,z3,z106,z20]),(0,[z1,z2,z3,z33,z20,z27]),(0,[z1,z1481,z2,z3,z5,z6])],[(0,[z36,z2,z4,z33,z5,z6]),(0,[z1,z2,z3,z42,z5,z228]),(0,[z1,z2,z3,z42,z5,z505]),(0,[z1,z2,z3,z42,z8,z579])],[(0,[z17,z1,z3,z5,z754,z6]),(0,[z1,z2,z32,z3,z42,z8]),(0,[z1482,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z53,z6,z157]),(0,[z1,z396,z2,z3,z42,z27])],[(0,[z1,z2,z3,z1483,z8,z6]),(0,[z1,z11,z2,z3,z215,z6]),(0,[z1,z11,z3,z356,z5,z6]),(0,[z1,z2,z3,z498,z6,z557])],[(0,[z1,z2,z3,z42,z21,z230]),(0,[z17,z1,z2,z48,z3,z42]),(0,[z1,z2,z3,z42,z87,z27])],[(0,[z1,z2,z3,z5,z246,z6]),(0,[z1,z11,z2,z3,z112,z6]),(0,[z1,z11,z2,z3,z42,z187])],[(0,[z1,z2,z3,z5,z6,z1484]),(0,[z1,z2,z3,z5,z1485,z6]),(0,[z1,z2,z3,z1486,z5,z6]),(0,[z1,z2,z71,z3,z432,z8]),(0,[z1487,z1,z2,z3,z5,z6]),(0,[z1274,z1,z2,z3,z42,z6])],[(0,[z1,z2,z3,z5,z29,z6]),(0,[z28,z2,z57,z3,z92,z6]),(0,[z116,z129,z2,z3,z5,z84]),(0,[z1488,z1,z2,z3,z128,z6]),(0,[z1,z2,z3,z5,z579,z27]),(0,[z1,z2,z3,z398,z42,z27])],[(0,[z1,z2,z3,z1089,z41,z6]),(0,[z1,z1489,z2,z3,z5,z6]),(0,[z116,z1,z2,z3,z5,z237])],[(0,[z17,z1,z3,z5,z156,z6]),(0,[z1,z2,z1490,z3,z5,z6]),(0,[z1,z2,z3,z5,z1491,z6]),(0,[z1,z2,z376,z5,z6,z69]),(0,[z1,z2,z3,z59,z34,z6])],[(0,[z1,z2,z3,z5,z331,z1492]),(0,[z1,z2,z3,z5,z6,z1493]),(0,[z17,z1,z2,z3,z718,z6]),(0,[z17,z1,z2,z26,z5,z69]),(0,[z1494,z1,z2,z3,z5,z6])],[(0,[z1,z962,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z1495,z6]),(0,[z1,z374,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1496,z6]),(0,[z1,z2,z57,z3,z401,z6]),(0,[z1,z2,z3,z91,z6,z27])],[(0,[z116,z1,z2,z3,z42,z10]),(0,[z1,z497,z3,z60,z5,z6]),(0,[z1,z2,z3,z418,z8,z20]),(0,[z1,z2,z3,z42,z38,z27]),(0,[z1,z2,z3,z1363,z5,z6]),(0,[z1,z2,z57,z3,z1351,z6])],[(0,[z1,z11,z2,z3,z1497,z6]),(0,[z17,z1,z3,z5,z6,z339])],[(0,[z1,z2,z3,z106,z41,z20])],[(0,[z1,z2,z3,z208,z401,z8])],[(0,[z1,z2,z3,z1498,z8,z6]),(0,[z17,z1,z2,z3,z123,z6]),(0,[z1,z2,z3,z1499,z5,z6]),(0,[z1,z177,z51,z5,z277,z6]),(0,[z1,z2,z3,z264,z34,z6]),(0,[z1,z2,z3,z42,z8,z216]),(0,[z1,z2,z1500,z3,z5,z6])],[(0,[z1,z329,z3,z8,z20,z6]),(0,[z2,z196,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z195,z27]),(0,[z1,z3,z5,z21,z6,z1211]),(0,[z1,z204,z2,z3,z42,z27]),(0,[z1501,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1502,z6]),(0,[z1,z2,z1503,z3,z5,z6]),(0,[z1504,z1,z2,z3,z5,z6])],[(0,[z494,z1,z60,z5,z8,z6]),(1,[z1,z2,z3,z42,z338]),(0,[z1,z2,z3,z33,z174,z6])],[(0,[z1,z2,z35,z5,z6,z27]),(0,[z1505,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z377,z20,z6]),(0,[z116,z15,z16,z3,z5,z6]),(0,[z1506,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z20,z6,z1507]),(0,[z1,z2,z3,z289,z8,z6])],[(0,[z1,z2,z3,z33,z5,z331]),(0,[z1,z2,z71,z40,z21,z6]),(0,[z1,z905,z60,z5,z8,z6]),(0,[z1,z2,z3,z5,z6,z1508]),(0,[z1,z2,z3,z42,z361,z6]),(0,[z1,z2,z3,z106,z5,z294])],[(0,[z1,z2,z3,z1509,z8,z6]),(0,[z1,z2,z3,z1510,z5,z6]),(0,[z1,z2,z3,z8,z20,z195]),(0,[z1,z2,z3,z42,z5,z27])],[(0,[z1,z11,z2,z3,z956,z6]),(0,[z116,z1,z2,z57,z42,z6])],[(0,[z2,z3,z5,z710,z21,z6]),(0,[z1,z2,z3,z42,z8,z228]),(0,[z1,z2,z3,z42,z8,z505]),(0,[z1,z2,z3,z8,z1511,z6]),(0,[z1,z2,z3,z1512,z5,z6]),(0,[z1,z2,z3,z5,z1513,z6])],[(0,[z1,z2,z3,z5,z6,z1514]),(0,[z1,z2,z3,z5,z8,z1515])]],
   [[],[(0,[z1,z2,z3,z1516,z5,z6]),(0,[z1,z2,z3,z464,z6,z228]),(0,[z58,z1,z2,z3,z8,z237])],[(0,[z43,z1,z60,z5,z6,z27]),(0,[z1,z2,z3,z5,z1517,z6]),(0,[z1,z2,z3,z42,z337,z6])],[(0,[z1,z2,z891,z5,z8,z6]),(0,[z1,z1518,z2,z3,z5,z6]),(0,[z1,z2,z3,z65,z6,z27]),(0,[z1,z11,z2,z3,z128,z6]),(0,[z1,z2,z3,z5,z308,z18]),(0,[z1,z2,z217,z5,z6,z297])],[(0,[z1,z2,z48,z3,z997,z8])],[(0,[z1,z2,z3,z1519,z5,z6]),(0,[z1,z2,z1520,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1521,z6]),(0,[z1,z3,z5,z1522,z8,z6])],[(0,[z1,z2,z3,z822,z8,z6]),(0,[z17,z1,z2,z1449,z5,z6])],[(0,[z1,z177,z51,z5,z41,z6]),(0,[z709,z1,z2,z3,z42,z6])],[(0,[z1,z2,z3,z5,z6,z557]),(0,[z1,z2,z3,z5,z1523,z6]),(0,[z1,z2,z57,z115,z20,z6])],[(0,[z1,z2,z3,z1524,z8,z6]),(0,[z1,z2,z3,z104,z21,z6]),(0,[z1,z2,z3,z5,z1433,z6]),(0,[z1,z2,z3,z432,z8,z20]),(0,[z1,z2,z3,z8,z482,z6]),(0,[z58,z1,z2,z3,z53,z68]),(0,[z1,z2,z3,z1525,z20,z6])],[(0,[z1,z2,z57,z3,z464,z6]),(0,[z116,z1,z2,z3,z42,z84]),(0,[z1,z2,z3,z1526,z65,z6]),(0,[z17,z1,z2,z3,z343,z5]),(0,[z1,z2,z3,z42,z69,z27])],[(0,[z1,z2,z35,z314,z8,z6]),(0,[z1,z2,z207,z3,z20,z6]),(0,[z1,z2,z3,z5,z1527,z6])],[(0,[z1,z266,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z1528,z6]),(0,[z1,z267,z11,z3,z5,z6]),(0,[z1,z44,z25,z3,z42,z8]),(0,[z1,z25,z3,z193,z5,z97])],[(0,[z1,z2,z3,z42,z377,z6]),(0,[z1,z2,z3,z1156,z41,z6]),(0,[z1257,z1,z2,z3,z401,z6])],[(0,[z1,z2,z3,z5,z6,z1529]),(0,[z1,z2,z3,z1530,z8,z6]),(0,[z116,z1,z2,z71,z40,z6]),(0,[z1,z2,z3,z375,z91,z6])],[(1,[z2,z3,z1342,z8,z6])],[(0,[z1,z2,z3,z5,z1531,z6]),(0,[z1,z44,z2,z3,z5,z310])],[(0,[z1,z2,z3,z5,z37,z27]),(0,[z9,z2,z3,z5,z474,z10]),(0,[z1532,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z73,z6])],[(0,[z1,z2,z993,z138,z5,z6]),(0,[z1,z2,z3,z1037,z8,z6]),(0,[z1,z2,z3,z5,z8,z1129]),(0,[z1533,z1,z2,z3,z5,z6]),(0,[z1,z44,z3,z8,z20,z70]),(0,[z1,z2,z3,z42,z8,z27])],[(0,[z1,z2,z3,z173,z41,z6]),(0,[z452,z2,z3,z359,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1534]),(0,[z1,z180,z2,z3,z20,z6])],[(0,[z1,z2,z1535,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1536])],[(0,[z1,z2,z165,z5,z72,z6])],[(0,[z1,z2,z3,z1537,z8,z6]),(0,[z1,z2,z3,z42,z158,z6]),(0,[z1,z2,z3,z1538,z5,z6]),(0,[z1,z178,z2,z212,z5,z6]),(0,[z1,z1539,z2,z3,z5,z6])],[(0,[z17,z1,z2,z730,z5,z6]),(0,[z1,z2,z3,z227,z20,z6]),(0,[z1,z2,z3,z42,z33,z6])],[(0,[z1,z2,z3,z5,z1540,z6]),(0,[z166,z1,z2,z3,z42,z5]),(0,[z166,z1,z2,z3,z112,z6]),(0,[z1,z2,z3,z42,z115,z27])],[(0,[z166,z1,z2,z3,z5,z310]),(0,[z1,z2,z3,z128,z6,z27])],[(0,[z1,z2,z152,z3,z42,z6]),(0,[z1,z2,z3,z42,z8,z301]),(0,[z116,z1,z2,z3,z1541,z5]),(0,[z1,z2,z3,z1332,z5,z6])],[(0,[z2,z3,z251,z5,z6,z84]),(0,[z1,z2,z3,z289,z8,z10]),(0,[z1,z2,z3,z5,z6,z1542]),(0,[z1,z1543,z2,z3,z5,z6])],[(0,[z17,z1,z2,z3,z1201,z5]),(0,[z1,z2,z3,z5,z1544,z6])],[(0,[z1,z1545,z2,z3,z5,z6]),(0,[z1,z2,z1546,z42,z8,z6])]],
   [[(0,[z1,z2,z3,z1547,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1548]),(0,[z1,z2,z3,z42,z960,z6]),(0,[z43,z1,z57,z60,z5,z6])],[(0,[z1,z2,z3,z254,z8,z206]),(0,[z36,z2,z4,z5,z461,z6]),(0,[z1,z2,z3,z5,z933,z6]),(0,[z1,z44,z374,z3,z5,z6]),(0,[z1,z2,z57,z3,z5,z1457]),(0,[z1,z2,z3,z33,z1437,z6])],[(0,[z1,z1549,z2,z3,z5,z6]),(0,[z36,z2,z4,z5,z8,z37]),(0,[z116,z1,z2,z3,z1550,z6])],[(0,[z1,z11,z2,z3,z314,z6]),(0,[z1,z2,z3,z5,z1551,z6])],[(0,[z1,z1552,z3,z5,z8,z6]),(0,[z107,z2,z3,z21,z20,z6]),(0,[z99,z1,z2,z3,z418,z5])],[(0,[z129,z2,z57,z3,z5,z84]),(0,[z1,z2,z3,z718,z8,z6])],[(0,[z1,z2,z3,z1553,z5,z6]),(0,[z1,z2,z3,z5,z10,z74]),(0,[z1,z11,z2,z3,z106,z20])],[(0,[z1,z2,z3,z5,z8,z1554]),(0,[z1555,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z59,z482,z6])],[(0,[z1,z2,z3,z42,z8,z487]),(0,[z1556,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z8,z660]),(0,[z1,z2,z3,z5,z944,z6]),(0,[z1,z2,z3,z42,z294,z6]),(0,[z1557,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z8,z1209,z450]),(0,[z1,z2,z3,z334,z20,z6]),(0,[z1,z25,z3,z5,z8,z769]),(0,[z1,z2,z3,z42,z8,z20]),(0,[z1,z2,z3,z1145,z20,z6])],[(0,[z1,z2,z3,z215,z474,z6]),(0,[z9,z2,z3,z5,z10,z505]),(0,[z1,z2,z3,z5,z1558,z6]),(0,[z1,z2,z3,z8,z419,z6]),(0,[z1,z2,z3,z42,z1559,z6])],[(0,[z1,z2,z3,z1560,z5,z8]),(0,[z1,z2,z3,z1561,z8,z6]),(0,[z1,z2,z3,z418,z40,z8]),(0,[z1,z44,z3,z253,z5,z8])],[(0,[z1,z2,z3,z5,z8,z1562]),(0,[z107,z2,z3,z42,z21,z6]),(0,[z1,z2,z3,z592,z5,z27]),(0,[z466,z1,z2,z71,z40,z6]),(0,[z1,z497,z2,z3,z482,z6])],[(0,[z1,z2,z3,z1563,z5,z6]),(0,[z129,z2,z3,z5,z21,z84])],[(0,[z137,z139,z57,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1564]),(0,[z1,z2,z217,z51,z5,z6]),(0,[z1,z572,z11,z3,z5,z6]),(0,[z1,z2,z3,z864,z8,z6]),(0,[z1,z2,z3,z5,z411,z27])],[(0,[z443,z1,z86,z3,z5,z6]),(0,[z1,z2,z217,z60,z5,z6]),(0,[z62,z1,z2,z239,z8,z6])],[(0,[z1,z2,z3,z33,z114,z6]),(0,[z1,z2,z3,z147,z5,z18]),(0,[z116,z1,z2,z3,z418,z5]),(0,[z1,z2,z3,z800,z8,z6]),(0,[z1,z429,z2,z3,z42,z8]),(0,[z58,z1,z2,z3,z308,z6]),(0,[z1,z2,z3,z5,z1565,z6])],[(0,[z1,z11,z2,z3,z401,z6]),(0,[z166,z1,z2,z3,z128,z6])],[(0,[z1,z2,z1175,z3,z5,z6]),(0,[z1,z2,z3,z33,z5,z326]),(0,[z1,z183,z11,z3,z5,z6]),(0,[z1,z2,z26,z3,z42,z103])],[(0,[z116,z1,z2,z3,z91,z6]),(0,[z1,z2,z3,z33,z5,z68])],[(0,[z1,z2,z3,z5,z1566,z6]),(0,[z590,z2,z3,z42,z8,z10]),(0,[z1,z2,z3,z20,z6,z74]),(0,[z1,z2,z3,z8,z34,z237])],[(0,[z1,z2,z3,z42,z45,z6]),(0,[z1,z1567,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z6,z1023]),(0,[z1,z497,z2,z3,z498,z6])],[(0,[z137,z139,z3,z5,z21,z6]),(0,[z1,z2,z3,z42,z287,z6]),(0,[z1,z2,z3,z33,z5,z311])],[(0,[z1,z2,z3,z521,z21,z6]),(0,[z1,z2,z3,z1138,z8,z6]),(0,[z1,z2,z965,z5,z8,z6]),(0,[z1,z2,z3,z53,z1391,z6])],[(0,[z1,z2,z3,z147,z20,z6]),(0,[z1,z2,z3,z462,z33,z6])],[(0,[z1,z2,z3,z5,z1568,z6]),(0,[z110,z365,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z208,z5])],[(0,[z116,z1,z2,z3,z215,z6]),(0,[z405,z2,z3,z5,z8,z10]),(0,[z1,z2,z3,z106,z8,z482]),(0,[z1,z1569,z2,z3,z5,z6])],[(0,[z1,z2,z3,z42,z33,z10]),(0,[z1,z2,z3,z42,z8,z570]),(0,[z1,z2,z48,z57,z5,z72])],[(0,[z1,z2,z3,z42,z8,z10]),(0,[z142,z1,z2,z3,z5,z6]),(0,[z17,z1,z2,z100,z101,z6]),(0,[z116,z1,z2,z3,z112,z6]),(0,[z116,z1,z2,z3,z42,z187]),(0,[z1,z2,z3,z5,z8,z1269])],[(0,[z1,z2,z3,z1570,z8,z6]),(0,[z1,z2,z3,z42,z8,z19])],[(0,[z1,z2,z5,z8,z1571,z6]),(0,[z1,z2,z313,z3,z42,z8]),(0,[z1,z2,z3,z42,z41,z326]),(0,[z1,z2,z3,z5,z8,z788]),(0,[z1,z2,z3,z1526,z5,z6]),(0,[z1,z183,z3,z5,z6,z70]),(0,[z1,z2,z57,z5,z771,z6]),(0,[z1,z2,z3,z1550,z6,z411])]],
   [[(0,[z1,z2,z1572,z5,z8,z6]),(0,[z1573,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z1574,z6]),(0,[z2,z3,z93,z1342,z8,z6])],[(0,[z1,z267,z3,z5,z8,z70]),(0,[z1,z2,z3,z300,z20,z6]),(0,[z1,z1575,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z1576])],[(0,[z1,z2,z3,z5,z1577,z6]),(0,[z590,z2,z3,z93,z8,z6]),(0,[z1,z2,z3,z5,z1578,z6]),(0,[z1,z555,z2,z3,z5,z74]),(0,[z1,z2,z71,z239,z8,z6])],[(0,[z1,z1579,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1580]),(0,[z1,z2,z3,z5,z1581,z6]),(0,[z1,z1582,z2,z3,z5,z6]),(0,[z1,z2,z26,z3,z42,z308]),(0,[z1,z1583,z2,z3,z5,z6]),(0,[z465,z1,z2,z3,z462,z6])],[(0,[z1,z2,z1584,z3,z5,z6]),(0,[z110,z1,z2,z3,z20,z6])],[(0,[z1,z2,z3,z5,z450,z1585]),(0,[z1,z2,z3,z418,z5,z21]),(0,[z166,z1,z2,z3,z1184,z6])],[(0,[z1,z2,z3,z5,z182,z27]),(1,[z1,z2,z3,z42,z45]),(0,[z1,z2,z48,z3,z42,z308]),(0,[z1,z2,z3,z498,z8,z6])],[(0,[z142,z1,z2,z3,z1117,z6]),(0,[z1,z2,z3,z5,z361,z6])],[(0,[z1,z2,z1586,z3,z5,z6]),(0,[z1,z2,z3,z106,z5,z338])],[(0,[z1,z329,z3,z5,z94,z6]),(0,[z1,z2,z3,z1530,z6,z74])],[(0,[z1,z56,z3,z89,z6,z27])],[(0,[z1,z329,z3,z104,z8,z6]),(0,[z1,z2,z3,z5,z1587,z6]),(0,[z1,z2,z3,z174,z41,z6])],[(0,[z1,z2,z3,z5,z1237,z6]),(0,[z17,z1,z2,z3,z5,z195]),(0,[z1,z2,z3,z884,z5,z80]),(0,[z1,z1588,z2,z3,z5,z6]),(0,[z1,z11,z2,z3,z464,z6]),(0,[z99,z1,z2,z3,z20,z6])],[(0,[z1,z1589,z2,z3,z5,z6]),(0,[z1,z2,z3,z21,z1194,z6]),(0,[z1,z2,z3,z5,z423,z6])],[(0,[z1590,z1,z266,z3,z5,z6]),(0,[z1591,z1,z2,z3,z5,z6]),(0,[z1,z2,z1592,z3,z5,z6]),(0,[z219,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z8,z413]),(0,[z1,z2,z3,z106,z120,z20])],[(0,[z1,z2,z1593,z3,z5,z8]),(0,[z1,z2,z3,z1594,z8,z6])],[(0,[z1,z2,z3,z289,z21,z6]),(0,[z1,z1344,z2,z3,z5,z6]),(0,[z116,z1,z2,z5,z606,z6]),(0,[z1,z2,z3,z5,z97,z338])],[(0,[z1,z2,z3,z1595,z5,z6]),(0,[z1,z1596,z2,z3,z5,z6]),(0,[z1,z2,z3,z1303,z20,z6])],[(0,[z1,z2,z3,z42,z8,z406]),(0,[z1,z3,z1208,z5,z8,z6]),(0,[z1,z2,z3,z5,z1597,z6]),(0,[z1,z2,z3,z416,z42,z27]),(0,[z1,z2,z3,z5,z6,z1598])],[(0,[z1,z2,z3,z733,z8,z6]),(1,[z738,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z6,z1599])],[(0,[z1,z2,z3,z418,z93,z8]),(0,[z1,z2,z3,z42,z21,z228]),(0,[z1,z2,z3,z42,z6,z74]),(0,[z1600,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z42,z78,z6]),(1,[z1,z3,z5,z8,z769]),(0,[z116,z1,z2,z3,z128,z6]),(0,[z1,z2,z342,z3,z42,z8])],[(0,[z1,z2,z3,z42,z8,z84]),(0,[z1,z2,z3,z5,z1012,z6])],[(0,[z1,z2,z3,z295,z20,z6]),(0,[z1,z2,z3,z33,z5,z37]),(0,[z2,z3,z5,z682,z21,z6]),(0,[z1,z2,z3,z112,z6,z27])],[(0,[z1,z2,z3,z8,z1601,z6]),(0,[z1,z2,z3,z5,z1602,z6]),(0,[z116,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z656,z67,z6])],[(0,[z1,z2,z3,z5,z8,z1603]),(0,[z28,z2,z3,z92,z6,z27]),(0,[z1604,z1,z2,z3,z5,z6]),(0,[z1,z183,z25,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1605])],[(0,[z1,z2,z3,z1606,z5,z6]),(0,[z1,z2,z3,z8,z67,z6]),(0,[z1,z2,z47,z3,z42,z6])],[(0,[z1,z2,z3,z33,z5,z450]),(0,[z1,z266,z57,z3,z5,z6]),(0,[z0,z1,z2,z3,z20,z6]),(0,[z1,z2,z695,z3,z42,z8]),(0,[z1,z2,z3,z1314,z464,z6])],[(0,[z1,z1607,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1608,z6])],[(0,[z1,z2,z3,z1609,z8,z6]),(0,[z2,z3,z5,z574,z41,z6]),(0,[z1,z2,z3,z42,z8,z638]),(0,[z1,z25,z3,z593,z5,z8]),(0,[z1,z2,z217,z3,z106,z5])],[(0,[z1,z2,z3,z93,z8,z80]),(0,[z1,z11,z3,z5,z280,z6]),(0,[z1,z2,z3,z5,z8,z1023]),(0,[z1,z1610,z2,z3,z20,z6])],[(0,[z1,z2,z3,z5,z501,z331]),(0,[z1,z2,z1611,z3,z5,z6]),(0,[z1,z2,z3,z5,z1612,z6]),(0,[z1,z354,z2,z3,z637,z6]),(0,[z1,z25,z2,z3,z5,z74]),(0,[z1,z2,z5,z88,z771,z6]),(0,[z1,z2,z3,z1613,z20,z6])]],
   [[(0,[z1,z2,z3,z5,z1614,z6]),(0,[z131,z2,z3,z93,z8,z6]),(0,[z1,z2,z3,z5,z80,z27]),(1,[z1,z3,z5,z754,z6])],[],[(0,[z1,z2,z3,z1615,z5,z6]),(0,[z382,z1,z2,z152,z5,z6]),(0,[z1,z2,z3,z281,z41,z6]),(0,[z1,z916,z2,z3,z5,z6]),(0,[z1,z2,z3,z1066,z5,z6]),(0,[z1,z1399,z2,z3,z42,z6]),(0,[z1,z2,z3,z5,z1616,z6])],[(0,[z1,z2,z35,z42,z8,z6]),(0,[z1,z2,z3,z5,z1617,z6]),(0,[z1,z2,z3,z957,z8,z6]),(0,[z1618,z1,z2,z3,z5,z6]),(0,[z164,z1,z2,z3,z42,z27])],[(0,[z1,z2,z3,z1261,z8,z6]),(0,[z1,z25,z3,z5,z97,z260])],[(0,[z1,z2,z3,z5,z6,z987]),(0,[z1,z2,z3,z1619,z5,z6]),(0,[z1,z2,z3,z5,z6,z1507]),(0,[z1620,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z5,z74]),(0,[z1,z2,z3,z112,z906,z6]),(0,[z1,z2,z3,z208,z8,z20])],[(0,[z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z1621,z8,z6]),(0,[z1,z1622,z3,z5,z8,z6]),(0,[z1,z3,z5,z8,z6,z1623])],[(0,[z1,z2,z3,z5,z1624,z6]),(0,[z382,z1,z2,z3,z42,z6]),(0,[z129,z11,z2,z3,z5,z84])],[],[(0,[z1,z2,z3,z42,z21,z27]),(0,[z2,z3,z5,z1625,z8,z6]),(0,[z1,z2,z3,z5,z1626,z6]),(0,[z1,z2,z3,z33,z5,z12]),(0,[z1,z2,z3,z5,z1627,z6]),(0,[z1,z2,z47,z3,z174,z6])],[],[(0,[z1,z2,z1546,z5,z8,z6]),(0,[z43,z1,z60,z42,z8,z6]),(0,[z1,z1059,z3,z42,z8,z6])],[(0,[z1,z2,z3,z432,z93,z8]),(0,[z62,z1,z2,z3,z42,z27])],[(0,[z1,z2,z858,z5,z8,z6]),(0,[z1,z2,z3,z359,z5,z326]),(0,[z1,z2,z3,z42,z1061,z6])],[],[(0,[z36,z2,z4,z5,z8,z206]),(0,[z151,z2,z49,z5,z41,z6]),(0,[z1628,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1038,z6]),(0,[z1,z2,z3,z215,z6,z27]),(0,[z1,z2,z3,z831,z5,z6])],[(0,[z1,z2,z3,z1629,z8,z6]),(0,[z325,z2,z4,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z1630]),(0,[z1,z191,z25,z2,z3,z42]),(0,[z1,z2,z376,z3,z462,z6])],[(0,[z1,z2,z3,z1275,z41,z6]),(0,[z17,z1,z177,z51,z5,z6])],[(0,[z1631,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z411,z84])],[(0,[z1,z2,z71,z40,z41,z6]),(0,[z1,z2,z627,z3,z42,z8]),(0,[z1,z2,z3,z5,z8,z1632]),(0,[z1,z2,z3,z33,z20,z6])],[(0,[z131,z2,z3,z93,z8,z80])],[(0,[z1633,z1,z2,z3,z5,z6]),(0,[z1,z177,z2,z165,z5,z6]),(0,[z17,z1,z374,z3,z5,z6]),(0,[z1,z2,z3,z5,z294,z6]),(0,[z1,z2,z3,z8,z20,z68])],[(0,[z1,z2,z3,z41,z482,z6]),(0,[z2,z3,z5,z8,z6,z1634]),(0,[z1,z2,z3,z1635,z5,z6]),(1,[z1,z2,z3,z42,z789])],[(0,[z1,z2,z3,z479,z20,z6]),(0,[z1,z2,z3,z5,z1559,z6])],[(0,[z1,z2,z3,z5,z6,z1636]),(0,[z1,z2,z26,z207,z5,z6]),(0,[z1,z2,z3,z174,z1637,z6]),(0,[z1,z1419,z2,z3,z42,z6])],[(0,[z137,z116,z139,z3,z5,z6]),(0,[z1590,z1,z2,z3,z5,z6]),(0,[z36,z2,z4,z5,z6,z27]),(0,[z36,z1,z2,z3,z42,z27]),(0,[z107,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z6,z1638]),(0,[z116,z1,z2,z3,z106,z20]),(0,[z1,z2,z3,z1639,z5,z6])],[(0,[z36,z2,z4,z5,z94,z6]),(0,[z1,z2,z3,z5,z8,z80]),(0,[z1,z2,z3,z5,z6,z1640]),(0,[z1,z2,z3,z1641,z8,z6]),(0,[z1,z2,z3,z5,z1642,z6])],[(0,[z1,z2,z3,z251,z5,z6]),(0,[z17,z1,z2,z3,z42,z6]),(0,[z1,z2,z3,z850,z8,z6]),(0,[z1,z2,z1643,z3,z5,z6])],[(0,[z1,z86,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z8,z74]),(0,[z1,z2,z71,z208,z40,z8])],[(0,[z1,z2,z1644,z3,z5,z6]),(0,[z9,z2,z3,z5,z73,z10]),(0,[z142,z1,z2,z3,z718,z6])],[(0,[z1,z2,z71,z3,z42,z27]),(0,[z1,z2,z3,z5,z1645,z6])],[(0,[z1,z2,z3,z5,z1646,z6]),(0,[z116,z1,z2,z42,z88,z6]),(0,[z1,z2,z3,z409,z42,z27])]],
   [[(0,[z1,z2,z3,z42,z21,z20]),(0,[z1,z2,z3,z5,z6,z1647]),(0,[z1,z2,z3,z1648,z5,z6]),(0,[z1,z2,z3,z1649,z8,z6]),(0,[z1,z442,z2,z3,z418,z8])],[(0,[z1,z2,z3,z1650,z5,z6]),(0,[z170,z1,z2,z3,z53,z6])],[(0,[z15,z1,z2,z3,z42,z27]),(0,[z1,z2,z3,z104,z41,z6]),(0,[z1,z1651,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z45,z6]),(0,[z1,z2,z3,z5,z291,z27]),(0,[z1,z2,z3,z5,z1652,z6])],[(0,[z1,z2,z3,z8,z909,z6])],[(0,[z186,z1,z2,z3,z42,z6]),(0,[z1,z3,z1208,z89,z8,z6]),(0,[z116,z1,z2,z3,z401,z6]),(0,[z1,z2,z1291,z3,z20,z6])],[(0,[z1,z2,z3,z1653,z8,z6]),(0,[z1,z2,z1654,z3,z5,z6]),(0,[z1,z2,z57,z3,z42,z338]),(0,[z1,z665,z2,z3,z42,z8]),(0,[z1247,z1,z2,z3,z5,z6])],[(0,[z28,z2,z3,z92,z158,z6])],[(0,[z1655,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1656,z6])],[(0,[z1,z2,z138,z42,z8,z6]),(0,[z1,z2,z3,z5,z206,z923]),(0,[z1,z2,z3,z1657,z8,z6]),(0,[z1,z2,z57,z3,z42,z18]),(0,[z1,z2,z3,z42,z8,z187])],[(0,[z15,z16,z3,z33,z5,z6]),(0,[z1,z2,z3,z5,z195,z1580]),(0,[z1,z44,z2,z3,z42,z41]),(0,[z1,z2,z3,z5,z31,z27]),(0,[z1,z2,z3,z1658,z8,z6])],[(0,[z1,z2,z3,z1659,z5,z6]),(0,[z1,z1660,z2,z3,z5,z6]),(0,[z1661,z1,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z174,z6]),(0,[z1,z2,z3,z1662,z20,z6])],[(0,[z1,z2,z3,z5,z1663,z6]),(0,[z1,z2,z3,z42,z8,z353]),(0,[z116,z1,z1664,z3,z5,z6]),(0,[z219,z1,z2,z217,z5,z6])],[(0,[z17,z1,z2,z3,z5,z331]),(0,[z1,z2,z3,z877,z8,z331]),(0,[z1,z2,z3,z1665,z5,z6]),(0,[z1666,z1,z2,z3,z5,z6])],[(0,[z17,z1,z391,z3,z5,z6]),(0,[z1,z3,z905,z5,z8,z6]),(0,[z17,z1,z2,z3,z1008,z6]),(0,[z1,z2,z3,z1351,z8,z6]),(0,[z1,z2,z3,z1231,z6,z27])],[(0,[z1,z2,z3,z5,z6,z1667]),(0,[z1,z2,z3,z5,z1668,z6]),(0,[z1,z2,z3,z42,z8,z168])],[(0,[z129,z2,z3,z8,z20,z84]),(0,[z43,z1,z374,z3,z5,z6]),(0,[z1076,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z8,z1381,z6]),(0,[z1,z2,z3,z5,z1669,z6]),(0,[z1,z3,z5,z754,z8,z6])],[],[(0,[z1,z2,z1670,z5,z8,z6]),(0,[z696,z1,z60,z5,z8,z6]),(0,[z1,z2,z3,z5,z461,z37]),(0,[z1,z2,z3,z1671,z8,z6]),(0,[z1,z1672,z2,z3,z5,z6]),(0,[z1,z2,z3,z277,z20,z6]),(0,[z1,z2,z730,z5,z8,z6]),(0,[z1,z2,z3,z5,z1673,z6])],[(0,[z1,z2,z3,z5,z1674,z6]),(0,[z17,z1,z679,z3,z5,z6])],[(0,[z116,z1,z2,z3,z776,z6])],[(0,[z28,z2,z3,z92,z29,z6]),(0,[z1,z2,z3,z106,z5,z45])],[(0,[z1,z2,z3,z5,z6,z1675]),(0,[z1,z2,z3,z5,z84,z338])],[(0,[z1,z2,z3,z41,z419,z6])],[(0,[z36,z2,z3,z503,z5,z6]),(0,[z1,z2,z3,z1510,z5,z195]),(0,[z1,z2,z3,z1676,z6,z581]),(0,[z43,z116,z1,z60,z5,z6]),(0,[z219,z1,z736,z3,z5,z6]),(0,[z1,z2,z3,z8,z1677,z6])],[(0,[z1,z2,z3,z1385,z5,z6]),(0,[z1,z2,z3,z5,z1678,z6]),(0,[z420,z2,z3,z8,z19,z6]),(0,[z1,z2,z3,z33,z498,z27])],[(0,[z443,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1679]),(0,[z1,z2,z3,z1680,z5,z6]),(0,[z1,z2,z3,z1681,z5,z8]),(0,[z1,z2,z3,z8,z20,z449])],[(0,[z1,z2,z3,z5,z1682,z6]),(0,[z28,z2,z3,z33,z92,z6]),(1,[z1,z2,z3,z42,z581]),(0,[z58,z1,z2,z3,z5,z68])],[(0,[z1,z1683,z2,z3,z5,z6]),(0,[z2,z3,z5,z21,z6,z557]),(0,[z1,z2,z3,z42,z8,z689]),(0,[z1,z191,z2,z3,z1246,z6]),(0,[z1,z2,z3,z1684,z5,z6])],[(0,[z1,z2,z3,z8,z1685,z6]),(0,[z151,z2,z49,z33,z5,z6]),(0,[z1,z2,z1686,z3,z5,z6]),(0,[z2,z3,z1342,z5,z8,z6]),(0,[z1,z2,z1687,z3,z5,z6]),(0,[z1688,z1,z2,z3,z5,z6])],[(0,[z116,z1,z2,z3,z464,z6]),(0,[z17,z1,z2,z3,z42,z10]),(0,[z1,z2,z3,z1130,z5,z8]),(0,[z1,z2,z1689,z3,z5,z6])],[(0,[z1,z2,z3,z314,z8,z331]),(0,[z1,z2,z3,z5,z1613,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z74]),(0,[z278,z1,z2,z3,z42,z27])],[(0,[z912,z1,z2,z35,z5,z6]),(0,[z15,z2,z3,z503,z5,z6]),(0,[z1,z2,z3,z752,z147,z6]),(0,[z116,z1,z2,z545,z5,z6])],[(0,[z1,z2,z3,z1690,z5,z6]),(0,[z1,z2,z3,z444,z20,z6]),(0,[z116,z1,z2,z3,z5,z1434])],[(0,[z1,z2,z3,z33,z5,z206]),(0,[z58,z1,z2,z3,z1391,z6])],[(0,[z1691,z1,z2,z3,z5,z6]),(0,[z1,z1692,z3,z5,z8,z6]),(0,[z17,z131,z2,z3,z93,z6]),(0,[z1,z2,z376,z47,z5,z6]),(0,[z1,z2,z3,z53,z103,z6])],[(0,[z1,z2,z3,z5,z353,z27]),(0,[z1,z2,z3,z1693,z5,z6]),(0,[z1,z2,z57,z3,z173,z6])],[(0,[z129,z2,z3,z5,z41,z84]),(0,[z1,z1694,z2,z3,z5,z6]),(0,[z1,z2,z26,z488,z5,z69])],[(0,[z1,z2,z100,z3,z432,z8]),(0,[z1,z2,z26,z3,z42,z33]),(0,[z1,z2,z3,z42,z1137,z6]),(0,[z1,z2,z3,z42,z308,z27]),(0,[z303,z1,z2,z3,z42,z27])],[(0,[z1,z2,z3,z1695,z8,z6]),(0,[z747,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z5,z1696,z6]),(0,[z600,z2,z3,z252,z8,z6])],[(0,[z1,z2,z3,z5,z1697,z6]),(0,[z1,z2,z3,z1698,z5,z6])],[(0,[z1699,z1,z2,z3,z5,z6]),(0,[z129,z2,z3,z5,z84,z228]),(0,[z1,z2,z48,z3,z42,z33])],[(0,[z1,z2,z3,z5,z1700,z6]),(0,[z1,z722,z3,z5,z6,z27])],[(0,[z1,z2,z1701,z3,z5,z6]),(0,[z1,z2,z3,z42,z21,z84]),(0,[z1,z2,z3,z33,z976,z6])],[(0,[z1,z2,z3,z5,z6,z1702]),(0,[z1,z2,z1703,z3,z5,z6]),(0,[z24,z1,z2,z3,z5,z6]),(0,[z1,z2,z1704,z3,z5,z6]),(0,[z1,z44,z3,z289,z8,z70]),(0,[z1,z2,z3,z1042,z8,z6]),(0,[z1,z2,z3,z1194,z6,z27])],[(0,[z1,z2,z3,z5,z8,z1705]),(0,[z1,z2,z3,z5,z1706,z6]),(0,[z1,z2,z165,z4,z5,z6]),(0,[z1,z2,z3,z21,z464,z6]),(0,[z129,z2,z3,z5,z50,z84])],[(0,[z137,z139,z3,z5,z41,z6]),(0,[z1,z2,z3,z5,z1707,z6]),(0,[z1,z2,z3,z563,z20,z6]),(0,[z1,z191,z2,z3,z5,z6])],[(0,[z1,z2,z3,z123,z8,z6]),(0,[z1,z2,z3,z521,z41,z6]),(0,[z1,z2,z3,z5,z6,z1708]),(0,[z1,z497,z2,z3,z42,z27])],[(0,[z1709,z1,z2,z3,z5,z6]),(0,[z1,z2,z742,z5,z8,z6])],[(0,[z1,z2,z196,z3,z5,z6]),(0,[z1,z2,z3,z8,z952,z6])],[(0,[z1,z2,z3,z5,z1710,z6]),(0,[z1,z2,z3,z1711,z5,z6]),(0,[z2,z3,z5,z41,z21,z6]),(0,[z1,z2,z3,z432,z5,z1318]),(0,[z1442,z1,z2,z3,z5,z6])],[(0,[z1,z2,z57,z3,z5,z6]),(0,[z1,z2,z49,z3,z42,z27])],[(0,[z1,z1712,z3,z5,z8,z6]),(0,[z43,z1,z11,z60,z5,z6])],[(0,[z2,z3,z742,z5,z8,z6]),(0,[z17,z1,z373,z3,z5,z6]),(0,[z17,z1,z44,z3,z5,z70])],[(0,[z43,z1,z60,z5,z8,z6]),(0,[z1,z11,z2,z3,z5,z1554]),(0,[z17,z1,z2,z3,z462,z6])],[(0,[z1,z66,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1713,z6]),(0,[z1,z2,z3,z208,z5,z21]),(0,[z1,z2,z3,z208,z5,z8])],[(0,[z1,z2,z26,z5,z8,z1269])],[(0,[z1,z2,z3,z5,z8,z1714]),(0,[z1,z2,z3,z5,z1715,z6]),(0,[z1,z2,z3,z1716,z8,z6])],[(0,[z1,z2,z3,z1717,z5,z6]),(0,[z1,z2,z26,z42,z8,z69]),(0,[z1494,z1,z2,z3,z42,z6])],[(0,[z1,z2,z3,z5,z1718,z6]),(0,[z1,z2,z3,z8,z1676,z6])],[(0,[z1,z2,z3,z42,z77,z27]),(0,[z1,z2,z376,z3,z20,z6])],[(0,[z17,z1,z497,z3,z5,z6]),(0,[z1,z2,z3,z42,z308,z20]),(1,[z1,z2,z3,z42,z557]),(0,[z1,z2,z3,z935,z20,z6])],[(0,[z1,z2,z3,z5,z501,z450]),(0,[z1,z2,z3,z1719,z8,z6]),(0,[z129,z2,z3,z5,z84,z27]),(0,[z9,z2,z3,z42,z8,z10])]],
   [[(0,[z1,z2,z3,z5,z1720,z6]),(0,[z640,z2,z3,z5,z8,z84]),(0,[z1,z2,z3,z418,z5,z423]),(0,[z1,z2,z3,z8,z1023,z187]),(0,[z278,z2,z3,z5,z6,z557])],[(0,[z9,z2,z3,z5,z8,z788]),(0,[z1721,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z8,z1722,z6]),(0,[z17,z1,z2,z758,z5,z6]),(0,[z1,z2,z3,z289,z344,z6]),(0,[z1,z1664,z3,z5,z8,z6])],[(0,[z17,z1,z2,z3,z114,z6]),(0,[z1,z2,z3,z5,z1723,z6]),(0,[z1,z2,z3,z1391,z34,z6])],[(0,[z1724,z1,z2,z3,z5,z6]),(0,[z1,z2,z858,z5,z21,z6]),(0,[z1,z180,z51,z3,z5,z6]),(0,[z1,z2,z3,z42,z1725,z6])],[(0,[z214,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z1726,z6]),(0,[z17,z1,z2,z26,z3,z42]),(0,[z1,z2,z100,z101,z6,z27]),(0,[z1,z2,z26,z3,z173,z8])],[(0,[z137,z1,z2,z3,z42,z27]),(0,[z1,z2,z1727,z5,z8,z6]),(0,[z17,z1,z2,z3,z5,z68]),(0,[z1,z2,z3,z5,z1153,z6]),(0,[z58,z1,z2,z3,z120,z6]),(0,[z1,z2,z3,z1728,z20,z6])],[(0,[z1,z1729,z2,z3,z5,z6]),(0,[z1,z2,z3,z41,z67,z6]),(0,[z1,z2,z3,z42,z8,z464]),(0,[z1,z2,z1730,z3,z5,z6]),(0,[z1,z2,z3,z1731,z8,z6]),(0,[z737,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z1732]),(0,[z1733,z2,z3,z5,z8,z6]),(0,[z1,z11,z2,z3,z42,z12])],[(0,[z1,z2,z57,z3,z5,z80]),(0,[z1,z2,z3,z289,z41,z6]),(0,[z1,z1734,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z8,z1735]),(0,[z1,z2,z3,z1208,z8,z6]),(0,[z1,z11,z2,z3,z42,z18]),(0,[z1,z2,z3,z1736,z5,z6])],[(0,[z15,z16,z3,z8,z20,z6]),(0,[z1,z11,z266,z3,z5,z6]),(0,[z1737,z1,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z5,z707]),(0,[z1,z2,z3,z5,z8,z237])],[(0,[z1,z2,z3,z5,z6,z1492]),(0,[z1,z2,z3,z5,z1738,z6]),(0,[z1,z2,z3,z1186,z6,z338]),(0,[z116,z1,z2,z5,z88,z6]),(0,[z1,z792,z2,z3,z20,z6])],[(0,[z1739,z1,z2,z3,z5,z6]),(0,[z1,z2,z376,z126,z5,z6])],[(0,[z1,z2,z3,z5,z41,z1515]),(0,[z1,z2,z3,z1438,z5,z6])],[(0,[z151,z1,z2,z3,z42,z27]),(0,[z1,z2,z57,z3,z521,z6]),(0,[z219,z1,z2,z5,z6,z77])],[(0,[z231,z2,z3,z5,z21,z6]),(0,[z1,z2,z3,z5,z6,z1740])],[(0,[z1,z2,z691,z3,z42,z8]),(0,[z1,z2,z3,z5,z6,z1741]),(0,[z1,z2,z3,z128,z8,z6]),(0,[z1,z2,z3,z1742,z5,z6]),(0,[z1,z1651,z57,z3,z5,z6])],[(0,[z1,z2,z35,z114,z8,z6]),(0,[z1,z2,z3,z42,z308,z10]),(0,[z1,z177,z2,z212,z5,z6]),(0,[z1,z11,z3,z5,z393,z6])],[(0,[z1,z2,z3,z5,z1743,z6]),(0,[z116,z1,z2,z5,z771,z6])],[(0,[z17,z1,z3,z42,z149,z6]),(0,[z1,z2,z3,z42,z253,z27])],[(0,[z2,z738,z3,z5,z8,z6]),(0,[z1,z2,z3,z1744,z5,z6]),(0,[z1,z2,z3,z5,z1745,z6]),(0,[z1746,z1,z2,z3,z5,z6]),(0,[z17,z1,z3,z5,z273,z6]),(0,[z1,z2,z3,z33,z1026,z6])],[(0,[z36,z266,z4,z5,z8,z6]),(0,[z129,z2,z3,z8,z464,z84]),(0,[z1,z180,z604,z3,z5,z6]),(0,[z1,z2,z3,z33,z5,z27])],[(0,[z1,z2,z3,z503,z20,z6]),(0,[z1,z2,z26,z5,z656,z69]),(0,[z1,z2,z3,z5,z1728,z6])],[(1,[z1,z2,z3,z42,z505])],[(0,[z1,z1747,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1406,z5,z450]),(0,[z1,z1748,z3,z5,z8,z6]),(0,[z1,z2,z476,z3,z42,z8]),(0,[z131,z2,z57,z3,z93,z6]),(0,[z1,z1749,z2,z3,z5,z6])],[(0,[z1,z2,z3,z215,z8,z84]),(0,[z1,z2,z3,z33,z18,z20])],[(0,[z1,z266,z3,z5,z41,z6])],[(0,[z1,z1750,z2,z3,z5,z6]),(0,[z1,z2,z3,z1089,z33,z6])],[(0,[z382,z1,z2,z5,z88,z6]),(0,[z1,z2,z3,z42,z288,z6]),(0,[z1,z2,z3,z418,z101,z8]),(0,[z1,z11,z3,z102,z5,z6])],[(0,[z1,z2,z3,z5,z461,z206]),(0,[z1,z2,z3,z42,z21,z187]),(0,[z2,z3,z5,z8,z788,z84]),(0,[z1,z2,z3,z5,z1047,z6]),(0,[z1,z44,z3,z8,z419,z70])],[(0,[z1488,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z2,z1751,z5,z8,z6]),(0,[z1,z2,z3,z5,z1752,z6]),(0,[z1,z2,z3,z1753,z5,z6]),(0,[z1,z2,z100,z8,z559,z6])],[(0,[z43,z17,z1,z60,z5,z6]),(0,[z1,z2,z3,z42,z1204,z6])],[(0,[z36,z2,z4,z42,z8,z6]),(0,[z1,z11,z2,z3,z1246,z6])],[(0,[z1,z2,z3,z1754,z8,z6]),(0,[z1,z1755,z2,z3,z5,z6])],[(0,[z1,z2,z3,z8,z20,z206]),(0,[z1,z2,z3,z1756,z5,z8]),(0,[z1,z2,z3,z1757,z5,z6])],[(0,[z1,z2,z3,z5,z1758,z6]),(0,[z1,z2,z3,z5,z6,z1759]),(0,[z1760,z1,z2,z3,z5,z6]),(0,[z1761,z1,z2,z3,z5,z6]),(0,[z166,z1,z25,z2,z3,z42])],[(0,[z1,z1324,z266,z3,z5,z6]),(0,[z1,z11,z2,z3,z173,z6]),(0,[z1,z2,z3,z5,z6,z1762])],[(1,[z1,z2,z3,z5,z744])],[(0,[z17,z1,z2,z3,z5,z37]),(0,[z1,z2,z3,z8,z1763,z6]),(0,[z1,z2,z3,z5,z1764,z6]),(0,[z1,z11,z2,z3,z5,z1603]),(0,[z1,z2,z3,z8,z1550,z6])],[],[(0,[z1,z2,z3,z5,z1765,z6]),(0,[z1,z2,z3,z5,z94,z37]),(0,[z1,z2,z3,z106,z5,z581]),(0,[z1,z2,z3,z42,z308,z84]),(0,[z1,z2,z3,z1766,z8,z6]),(0,[z1,z2,z3,z5,z1123,z6]),(0,[z1,z11,z3,z5,z198,z6]),(0,[z1,z2,z3,z5,z1767,z6])],[(0,[z1,z2,z3,z33,z281,z6]),(0,[z24,z1072,z2,z3,z5,z6])],[(0,[z17,z1,z2,z3,z5,z450]),(0,[z1,z2,z3,z8,z168,z237]),(0,[z1,z2,z3,z42,z8,z292])],[(0,[z1,z2,z3,z1768,z5,z6])],[(0,[z1,z2,z3,z78,z20,z6])],[(0,[z1,z2,z3,z501,z20,z6]),(0,[z1,z11,z2,z3,z1609,z6])],[(0,[z664,z2,z3,z92,z8,z6]),(0,[z1,z2,z3,z8,z1769,z6]),(0,[z1,z2,z3,z401,z6,z27])],[(0,[z1770,z1,z2,z3,z5,z6]),(0,[z350,z1,z2,z3,z42,z8]),(0,[z1,z2,z3,z5,z18,z310]),(0,[z1,z2,z3,z5,z1174,z6]),(0,[z1,z2,z1771,z3,z5,z6]),(0,[z1,z2,z3,z482,z6,z157])],[(0,[z1,z2,z3,z5,z1772,z6]),(0,[z28,z2,z3,z1342,z8,z6]),(0,[z1,z1692,z57,z3,z5,z6])],[(0,[z1,z2,z3,z42,z789,z27])],[(0,[z1,z2,z3,z5,z1773,z6]),(0,[z1,z2,z3,z1774,z5,z6])],[(0,[z1,z11,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1775]),(0,[z1,z2,z3,z446,z5,z27])],[(0,[z1,z2,z3,z42,z8,z331]),(0,[z116,z1,z2,z3,z1349,z5]),(0,[z1,z2,z3,z908,z5,z6])],[(0,[z1,z2,z3,z5,z1776,z6]),(0,[z1,z2,z3,z5,z1777,z6]),(0,[z1,z1778,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z97,z27]),(0,[z1,z2,z3,z42,z831,z6])],[(0,[z1,z2,z3,z1367,z5,z206]),(0,[z1,z2,z3,z5,z8,z1779]),(0,[z1,z2,z3,z42,z41,z20]),(0,[z99,z1,z56,z3,z89,z6]),(1,[z166,z1,z2,z3,z42])],[(0,[z17,z1,z2,z3,z5,z777]),(0,[z1,z2,z3,z106,z401,z8])],[(0,[z1,z2,z3,z5,z6,z1585]),(0,[z470,z2,z3,z5,z41,z6]),(0,[z1,z2,z57,z3,z123,z6]),(0,[z1,z2,z3,z5,z308,z6])],[(0,[z1,z2,z207,z3,z5,z6]),(0,[z1,z2,z3,z5,z1662,z6]),(0,[z1,z2,z3,z5,z669,z27]),(0,[z1,z2,z3,z5,z8,z1780]),(0,[z1,z11,z2,z3,z1530,z6]),(0,[z1,z2,z26,z8,z67,z69])],[(0,[z131,z2,z3,z93,z8,z195]),(0,[z1,z2,z3,z91,z21,z6]),(0,[z1,z2,z3,z1781,z5,z6]),(0,[z1,z2,z3,z418,z5,z1782]),(0,[z540,z2,z152,z3,z5,z6])],[(0,[z1,z329,z3,z5,z8,z6]),(0,[z1,z2,z385,z3,z20,z6]),(0,[z1,z2,z3,z33,z254,z6]),(0,[z2,z49,z3,z503,z5,z6]),(0,[z1,z2,z3,z5,z6,z1783]),(0,[z1,z2,z3,z318,z5,z27]),(0,[z1,z2,z3,z5,z6,z744])],[(0,[z433,z2,z3,z5,z41,z6]),(0,[z1,z2,z3,z8,z1784,z6]),(0,[z1,z2,z1785,z3,z5,z6])],[(0,[z1,z2,z3,z314,z8,z450]),(0,[z1,z2,z3,z5,z1786,z6]),(0,[z1,z218,z2,z3,z20,z6]),(0,[z1,z2,z3,z5,z10,z310])]],
   [[(0,[z1787,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z300,z6]),(0,[z1,z2,z3,z5,z6,z1788])],[(0,[z1,z2,z3,z1789,z8,z6])],[(0,[z1,z2,z3,z5,z8,z195]),(0,[z1,z2,z3,z1790,z5,z6]),(0,[z1,z2,z3,z8,z1194,z6]),(0,[z142,z1,z374,z3,z5,z6]),(0,[z1,z2,z3,z5,z1791,z6]),(0,[z1,z2,z3,z173,z33,z6])],[(0,[z1,z2,z1792,z3,z5,z6]),(0,[z1,z2,z3,z5,z1793,z6])],[(0,[z1,z2,z1794,z5,z8,z6]),(0,[z1,z2,z1795,z3,z5,z6]),(0,[z1,z180,z2,z3,z5,z6]),(0,[z17,z1,z2,z3,z20,z6]),(0,[z1,z44,z2,z3,z42,z308])],[(0,[z1,z2,z35,z5,z21,z6]),(0,[z1,z2,z3,z1796,z5,z6]),(0,[z466,z1,z2,z3,z432,z5]),(0,[z1,z2,z3,z5,z6,z1797])],[(0,[z1798,z1,z2,z3,z5,z6])],[(0,[z1,z2,z26,z5,z8,z69])],[(0,[z142,z1,z2,z3,z42,z6]),(0,[z116,z1,z25,z2,z3,z42]),(0,[z1,z2,z3,z227,z5,z6])],[(0,[z1,z11,z2,z3,z5,z80]),(0,[z1,z2,z3,z358,z5,z228]),(0,[z1,z2,z3,z1541,z5,z8]),(0,[z1,z2,z209,z3,z42,z8])],[(0,[z1,z2,z3,z33,z5,z581]),(0,[z1,z2,z3,z8,z1497,z6])],[(0,[z1,z2,z3,z184,z236,z6]),(0,[z1,z2,z3,z42,z41,z10]),(0,[z1,z1799,z2,z3,z5,z6]),(0,[z1,z25,z497,z3,z5,z6]),(0,[z1,z2,z3,z174,z6,z27]),(0,[z1,z2,z3,z42,z8,z352])],[(0,[z1,z2,z3,z5,z1800,z6]),(0,[z1,z11,z3,z5,z473,z6])],[(0,[z43,z1,z60,z5,z21,z6]),(0,[z1,z11,z2,z3,z289,z6]),(0,[z17,z1,z2,z3,z432,z5]),(0,[z1,z2,z3,z42,z8,z232]),(0,[z1,z2,z3,z106,z5,z557])],[(0,[z28,z2,z3,z92,z8,z6]),(0,[z1,z2,z3,z65,z21,z6]),(0,[z1,z2,z3,z5,z10,z338]),(0,[z1,z25,z2,z758,z5,z6]),(0,[z1,z2,z3,z5,z1801,z6])],[(0,[z1,z2,z3,z5,z1802,z6]),(0,[z1,z177,z514,z5,z8,z6]),(0,[z7,z1,z2,z5,z229,z6]),(0,[z1,z11,z2,z3,z521,z6]),(0,[z1,z2,z3,z5,z1725,z6]),(0,[z1,z2,z3,z20,z6,z1298])],[(0,[z1,z2,z3,z1803,z5,z6]),(0,[z1,z2,z3,z33,z5,z413])],[(0,[z1,z44,z218,z3,z5,z6]),(0,[z129,z2,z3,z521,z8,z84]),(0,[z1,z2,z899,z3,z20,z6])],[(0,[z166,z1,z2,z3,z850,z6]),(0,[z116,z1,z2,z3,z837,z6]),(0,[z1,z2,z3,z816,z6,z27])],[(0,[z1,z2,z3,z5,z1804,z6]),(0,[z324,z1,z2,z3,z42,z8])],[(0,[z1,z2,z3,z33,z5,z406]),(0,[z1,z2,z3,z498,z41,z6]),(0,[z1,z2,z3,z1341,z20,z6])],[(0,[z1,z2,z261,z3,z42,z27]),(0,[z1,z2,z3,z33,z91,z18])],[(0,[z1,z1805,z2,z3,z5,z6]),(0,[z1,z2,z3,z914,z8,z6])],[(0,[z1,z2,z3,z5,z1806,z6]),(0,[z1,z2,z3,z59,z91,z6])],[(0,[z1,z2,z3,z5,z1807,z6]),(0,[z1,z2,z3,z5,z6,z1808]),(0,[z1,z2,z57,z3,z5,z237])],[(0,[z1,z2,z3,z5,z331,z27]),(0,[z1,z44,z3,z5,z8,z70]),(0,[z219,z1,z2,z3,z42,z6])],[(0,[z131,z11,z2,z3,z93,z6])],[(0,[z15,z16,z3,z5,z6,z27]),(0,[z116,z1,z2,z3,z42,z18]),(0,[z1,z2,z3,z656,z20,z6])],[(0,[z116,z1,z266,z3,z5,z6]),(0,[z1,z2,z47,z3,z976,z6]),(0,[z1,z2,z913,z3,z20,z6]),(0,[z1,z2,z3,z5,z6,z157]),(0,[z1,z2,z3,z42,z308,z187])],[(0,[z1809,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z33,z482,z6])],[(0,[z1,z2,z3,z358,z5,z27])],[(0,[z1810,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z42,z198,z27]),(0,[z1,z2,z3,z42,z208,z8]),(0,[z1,z2,z3,z5,z1525,z6]),(0,[z1,z2,z3,z8,z482,z68])]],
   [[(0,[z1,z2,z3,z436,z20,z6]),(0,[z1,z2,z48,z3,z42,z27])],[(0,[z1,z2,z1811,z3,z5,z6])],[(0,[z1,z2,z3,z1120,z8,z6]),(0,[z1,z2,z3,z5,z277,z6]),(0,[z1,z2,z3,z281,z6,z27]),(0,[z1,z2,z3,z53,z498,z6])],[(0,[z1,z2,z3,z314,z501,z6]),(0,[z36,z2,z4,z254,z8,z6]),(0,[z1,z2,z3,z42,z300,z10]),(0,[z1,z2,z3,z362,z20,z6]),(0,[z1,z2,z3,z446,z8,z20])],[(0,[z1,z2,z3,z42,z8,z271]),(0,[z1,z2,z3,z42,z41,z84]),(0,[z166,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1812,z6]),(0,[z1,z497,z2,z3,z42,z5]),(0,[z1,z2,z3,z5,z8,z744]),(0,[z1,z2,z3,z251,z91,z6])],[(0,[z1,z2,z3,z128,z21,z6]),(0,[z1,z1813,z2,z3,z5,z6]),(0,[z1,z2,z3,z173,z8,z10]),(0,[z1,z2,z3,z106,z5,z505]),(0,[z1,z2,z3,z33,z498,z6])],[(0,[z129,z2,z3,z5,z444,z84]),(0,[z1,z2,z3,z5,z310,z27]),(0,[z1,z2,z3,z42,z702,z8])],[(0,[z1,z2,z3,z1814,z8,z6]),(0,[z1,z2,z3,z147,z5,z6]),(0,[z1,z2,z3,z1112,z8,z6]),(0,[z1,z2,z3,z41,z1676,z6]),(0,[z1,z2,z3,z42,z84,z228]),(0,[z219,z1,z2,z3,z174,z6])],[(0,[z1,z2,z3,z1815,z5,z8]),(0,[z1,z25,z2,z3,z42,z41])],[(0,[z1,z2,z138,z5,z8,z331]),(0,[z1,z2,z3,z5,z37,z1245]),(0,[z1,z2,z3,z5,z6,z1816]),(0,[z1817,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1818,z5,z6]),(0,[z43,z1,z143,z60,z5,z6]),(0,[z1,z2,z3,z1819,z5,z6])],[(0,[z1,z2,z3,z87,z5,z338])],[(0,[z1,z2,z3,z33,z5,z646]),(0,[z1,z11,z3,z5,z754,z6]),(0,[z1,z2,z3,z5,z344,z6]),(0,[z1,z2,z341,z3,z42,z8])],[(0,[z36,z2,z4,z5,z8,z6]),(0,[z1,z2,z3,z33,z65,z6]),(0,[z1,z1820,z3,z42,z8,z6])],[(0,[z151,z2,z49,z5,z6,z27]),(0,[z1,z2,z5,z771,z8,z6])],[(0,[z1,z2,z1453,z5,z8,z6]),(0,[z1821,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z300,z5,z6]),(0,[z1,z2,z3,z1822,z5,z6])],[(0,[z1,z2,z3,z5,z8,z1823]),(0,[z1,z177,z51,z42,z8,z6])],[(0,[z1,z2,z3,z1497,z6,z74]),(0,[z1,z2,z165,z5,z115,z6])],[(0,[z110,z1,z2,z3,z5,z6]),(0,[z1,z1337,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z20,z535])],[(0,[z1,z2,z3,z5,z41,z6]),(0,[z17,z1,z2,z3,z5,z206])],[(0,[z1,z2,z3,z5,z1824,z6]),(0,[z1,z2,z3,z423,z20,z6]),(0,[z1,z11,z2,z26,z5,z69]),(0,[z1,z44,z3,z5,z45,z70])],[(0,[z1,z2,z3,z5,z94,z206]),(0,[z1,z2,z1825,z3,z5,z6]),(0,[z1,z2,z3,z59,z30,z6]),(0,[z372,z66,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1826,z6]),(0,[z1,z2,z3,z5,z1827,z6]),(0,[z1,z204,z11,z3,z38,z6]),(0,[z1,z2,z3,z5,z1828,z6]),(0,[z1,z2,z3,z5,z1287,z6])],[(0,[z1,z2,z3,z104,z8,z206]),(0,[z1,z2,z3,z5,z1829,z6]),(0,[z17,z1,z11,z3,z5,z6]),(0,[z1,z2,z3,z1830,z5,z6]),(0,[z116,z1,z2,z209,z5,z6]),(0,[z116,z1,z2,z3,z173,z6]),(0,[z1,z2,z342,z8,z559,z6])],[(0,[z1,z2,z3,z5,z1831,z6]),(1,[z1,z2,z758,z5,z6]),(0,[z1,z2,z100,z3,z42,z27])],[(0,[z15,z86,z16,z3,z5,z6]),(0,[z1,z2,z3,z5,z1832,z6]),(0,[z1,z2,z3,z59,z6,z157])],[(0,[z1,z2,z3,z42,z1312,z6]),(0,[z1,z11,z2,z3,z123,z6]),(0,[z99,z1,z2,z3,z5,z6]),(0,[z1,z25,z3,z128,z8,z97]),(0,[z1,z2,z100,z57,z101,z6]),(0,[z1,z2,z3,z42,z6,z338])],[],[(0,[z1,z2,z1833,z5,z8,z6]),(0,[z1,z2,z3,z5,z1834,z6]),(0,[z1,z2,z3,z5,z8,z1835]),(0,[z1,z2,z3,z5,z6,z1414]),(0,[z1,z2,z3,z42,z84,z27]),(0,[z1,z1836,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1293,z6])],[(0,[z1,z1837,z3,z5,z8,z6]),(0,[z131,z2,z3,z93,z334,z6]),(0,[z1,z2,z3,z33,z419,z6]),(0,[z1,z2,z57,z3,z208,z5])],[(0,[z1,z2,z3,z5,z8,z1838]),(0,[z1,z2,z3,z5,z450,z27]),(0,[z1,z2,z3,z42,z8,z482])]],
   [[(0,[z1,z2,z3,z1391,z5,z6])],[(0,[z2,z3,z42,z41,z21,z6]),(0,[z1,z2,z3,z837,z6,z27])],[(0,[z1,z2,z3,z5,z8,z331]),(1,[z2,z3,z5,z8,z788]),(0,[z1,z2,z3,z1839,z5,z6]),(0,[z1,z25,z2,z3,z42,z8]),(0,[z1,z1301,z3,z5,z8,z6]),(0,[z286,z1,z2,z3,z42,z27])],[(0,[z9,z2,z3,z215,z8,z10]),(0,[z1,z2,z641,z3,z42,z8]),(0,[z1,z2,z1840,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1841,z6]),(0,[z1,z2,z3,z5,z334,z6]),(0,[z1,z2,z47,z3,z1026,z6]),(0,[z1,z2,z57,z5,z115,z6])],[(0,[z1,z266,z3,z5,z8,z37]),(1,[z1,z2,z3,z1391,z6])],[(0,[z1,z2,z3,z1842,z8,z6]),(0,[z1,z11,z509,z3,z5,z6]),(0,[z1,z2,z1643,z3,z42,z6])],[(0,[z116,z1,z2,z3,z5,z6]),(0,[z1,z86,z2,z3,z42,z6]),(0,[z1,z2,z3,z1843,z5,z6]),(0,[z1,z44,z3,z5,z8,z769])],[(0,[z1,z2,z3,z42,z8,z611]),(0,[z1,z2,z3,z5,z41,z80]),(0,[z1,z2,z3,z5,z74,z69]),(0,[z1,z2,z3,z42,z8,z336])],[(0,[z1,z2,z3,z314,z500,z6]),(0,[z1,z403,z2,z3,z42,z8])],[(0,[z1,z2,z138,z33,z5,z6]),(0,[z1267,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z20,z645]),(0,[z1,z2,z3,z5,z535,z27])],[(0,[z1,z2,z3,z147,z5,z10]),(0,[z1,z1844,z2,z3,z5,z6]),(0,[z1845,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z954,z5,z6])],[(0,[z1,z2,z3,z5,z8,z1846]),(0,[z1,z2,z3,z5,z6,z1847]),(0,[z7,z1,z2,z3,z42,z6]),(0,[z1,z2,z3,z42,z5,z338])],[(0,[z1,z2,z1848,z3,z5,z6]),(0,[z43,z1,z2,z165,z5,z6]),(0,[z1849,z1,z2,z3,z5,z6]),(0,[z1,z1610,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z8,z1850]),(0,[z1,z2,z3,z5,z1851,z6]),(0,[z116,z1,z2,z602,z5,z6])],[(0,[z1,z2,z3,z1852,z5,z8])],[(0,[z36,z2,z57,z4,z5,z6]),(0,[z1,z2,z3,z1342,z8,z6]),(0,[z1,z2,z57,z3,z5,z195]),(0,[z1,z2,z3,z1853,z5,z6]),(0,[z1,z2,z3,z5,z6,z1854]),(0,[z116,z1,z2,z489,z5,z6]),(0,[z1,z2,z3,z42,z557,z27])],[(0,[z1,z2,z3,z314,z6,z27]),(0,[z1,z2,z3,z42,z461,z6]),(0,[z1,z2,z3,z42,z8,z230]),(0,[z1,z2,z3,z42,z8,z383]),(0,[z43,z211,z1,z60,z5,z6]),(0,[z116,z1,z2,z3,z1117,z6]),(0,[z1,z2,z3,z106,z8,z1023])],[(0,[z1,z2,z3,z42,z8,z37]),(0,[z1,z2,z3,z42,z120,z20])],[(0,[z1,z2,z3,z1855,z8,z6]),(0,[z1,z2,z3,z5,z1856,z6]),(0,[z1,z2,z217,z5,z6,z69])],[(0,[z553,z2,z196,z3,z5,z6])],[(0,[z1,z2,z3,z33,z104,z6]),(0,[z1,z2,z3,z1857,z5,z6]),(0,[z1,z1858,z2,z3,z5,z6]),(0,[z1,z56,z3,z89,z21,z6]),(1,[z1,z2,z3,z42,z74]),(0,[z1,z11,z642,z3,z5,z6]),(0,[z1,z2,z261,z101,z8,z6])],[(0,[z1,z2,z3,z42,z8,z450]),(0,[z589,z2,z3,z93,z8,z6]),(0,[z116,z1,z2,z625,z5,z6]),(0,[z1,z2,z3,z42,z41,z187]),(0,[z1,z2,z3,z1859,z5,z6]),(0,[z1305,z1,z2,z3,z343,z5]),(0,[z1,z2,z3,z1369,z5,z6])],[(0,[z1,z2,z3,z1860,z8,z6]),(0,[z1,z2,z3,z1861,z5,z6]),(0,[z1,z2,z3,z5,z1862,z6]),(0,[z1,z2,z3,z1391,z8,z6])],[(0,[z1,z2,z3,z5,z334,z80]),(0,[z1,z2,z3,z5,z21,z195]),(0,[z1,z2,z3,z118,z30,z6]),(0,[z17,z9,z2,z3,z5,z10]),(0,[z1863,z1,z2,z3,z5,z6]),(0,[z1,z516,z2,z3,z42,z8])],[(0,[z1,z2,z3,z488,z20,z6]),(0,[z1,z2,z3,z20,z6,z811])],[(0,[z1,z2,z3,z5,z1864,z6]),(0,[z1,z1865,z2,z3,z5,z6]),(0,[z1,z2,z57,z3,z1210,z6])],[(0,[z1,z2,z3,z5,z1866,z6]),(0,[z116,z1,z2,z3,z5,z80]),(0,[z1,z2,z3,z1867,z5,z6]),(0,[z1,z2,z3,z1256,z208,z5])],[(0,[z1868,z1,z2,z3,z5,z6]),(0,[z1869,z1,z2,z3,z5,z6]),(0,[z17,z1,z3,z5,z290,z6]),(0,[z1,z2,z3,z42,z14,z6]),(0,[z1,z2,z3,z5,z8,z1870]),(0,[z1,z736,z3,z5,z8,z6])],[(0,[z1,z1871,z2,z3,z5,z6]),(0,[z1,z2,z26,z5,z21,z69]),(0,[z1,z2,z3,z5,z6,z411])],[(0,[z1,z2,z3,z5,z1872,z6]),(0,[z1,z2,z1873,z3,z5,z6]),(0,[z1,z2,z3,z5,z308,z237]),(1,[z1,z2,z217,z3,z42])],[]],
   [[(0,[z1,z2,z3,z5,z1874,z6]),(0,[z1,z2,z3,z42,z1261,z8]),(0,[z1,z2,z1875,z3,z5,z6]),(0,[z1,z722,z3,z5,z8,z6]),(0,[z1,z191,z3,z356,z5,z6])],[(0,[z1,z2,z244,z40,z8,z6]),(0,[z116,z1,z2,z3,z521,z6]),(0,[z1,z2,z3,z5,z1637,z6])],[(0,[z2,z139,z3,z503,z5,z6]),(0,[z1,z2,z1876,z3,z5,z6]),(1,[z1,z722,z3,z5,z6])],[(0,[z1,z2,z3,z1877,z8,z6]),(0,[z1,z2,z3,z8,z464,z6]),(0,[z1,z2,z3,z42,z147,z6]),(0,[z1,z2,z3,z1246,z8,z6]),(0,[z1,z2,z3,z42,z8,z338])],[(0,[z1,z2,z3,z114,z8,z331]),(0,[z28,z2,z3,z92,z21,z6]),(0,[z17,z1,z218,z3,z5,z6]),(0,[z1,z2,z3,z42,z474,z6]),(0,[z1,z2,z3,z42,z8,z12])],[(0,[z1878,z1,z2,z3,z5,z6]),(0,[z2,z3,z5,z710,z8,z6]),(0,[z1,z2,z57,z3,z215,z6]),(0,[z1,z2,z3,z103,z20,z6])],[(0,[z1,z2,z35,z8,z20,z6]),(0,[z131,z2,z3,z1342,z8,z6]),(0,[z1,z2,z57,z586,z5,z6]),(0,[z1,z2,z1879,z3,z5,z6]),(0,[z1,z2,z3,z5,z1880,z6]),(0,[z1,z2,z3,z942,z8,z6]),(0,[z1,z44,z2,z3,z42,z436]),(0,[z1,z2,z3,z42,z8,z18])],[(0,[z1,z2,z3,z169,z20,z6]),(0,[z1,z183,z191,z3,z5,z6]),(0,[z1,z44,z57,z3,z5,z70]),(0,[z166,z1,z3,z5,z6,z339]),(0,[z1,z1881,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1882,z6]),(0,[z1,z44,z2,z3,z42,z33])],[(0,[z1,z2,z3,z5,z1883,z6]),(0,[z1,z2,z3,z474,z20,z6])],[(0,[z1,z2,z3,z5,z310,z84]),(0,[z1,z2,z3,z1294,z5,z6]),(0,[z1,z2,z3,z5,z1884,z6]),(0,[z1,z2,z3,z970,z5,z6]),(0,[z1,z2,z3,z42,z252,z27]),(0,[z1,z2,z3,z42,z8,z683])],[],[(0,[z1,z2,z3,z5,z1885,z6]),(0,[z2,z3,z5,z8,z10,z788])],[(0,[z1,z132,z2,z3,z42,z8]),(0,[z16,z738,z3,z5,z8,z6]),(0,[z1,z2,z165,z3,z42,z6]),(0,[z219,z1,z2,z3,z5,z411]),(0,[z1,z2,z3,z33,z67,z6])],[(0,[z43,z1,z60,z8,z20,z6]),(0,[z1,z2,z3,z5,z8,z793])],[(0,[z1886,z1,z2,z3,z5,z6]),(0,[z137,z139,z3,z5,z6,z27]),(0,[z1887,z1,z2,z3,z5,z6]),(0,[z1,z183,z2,z3,z462,z6])],[],[(0,[z1888,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z990]),(0,[z1,z2,z3,z5,z1889,z6]),(0,[z43,z1,z2,z3,z725,z8]),(0,[z1,z2,z3,z5,z1890,z6])],[(0,[z1,z374,z139,z3,z5,z6]),(0,[z110,z1,z3,z5,z156,z6])],[(0,[z1,z177,z2,z3,z42,z27])],[(0,[z1891,z1,z2,z3,z5,z6])],[(0,[z140,z1,z2,z3,z202,z6])],[(0,[z1,z2,z3,z42,z50,z6]),(0,[z1,z2,z3,z462,z251,z6])],[(0,[z1,z1892,z2,z3,z5,z6]),(0,[z1,z492,z60,z5,z8,z6]),(0,[z1,z2,z3,z5,z1893,z6]),(0,[z1,z25,z3,z112,z8,z97])],[(0,[z561,z2,z3,z5,z21,z6]),(0,[z148,z231,z2,z3,z5,z6]),(0,[z24,z1,z2,z3,z42,z6])],[(0,[z1,z2,z3,z521,z893,z6]),(0,[z1,z2,z100,z101,z8,z6]),(0,[z1,z2,z3,z5,z1360,z6]),(0,[z1,z2,z3,z53,z75,z6])],[(0,[z1,z2,z3,z42,z501,z6]),(0,[z1,z1820,z3,z5,z8,z6]),(0,[z1,z2,z3,z215,z21,z6]),(0,[z1,z2,z3,z5,z1894,z6]),(0,[z1,z191,z2,z3,z42,z6]),(0,[z1,z191,z2,z3,z128,z6]),(0,[z1,z2,z3,z813,z8,z6]),(0,[z1,z2,z57,z3,z1186,z6]),(0,[z1,z2,z485,z3,z42,z8])],[(0,[z151,z2,z49,z5,z287,z6]),(0,[z1,z374,z3,z5,z97,z6]),(0,[z1,z2,z3,z5,z8,z68]),(0,[z590,z2,z3,z398,z8,z6]),(0,[z1,z2,z3,z120,z20,z6])],[(0,[z17,z1,z2,z3,z281,z6]),(0,[z1,z44,z2,z3,z5,z74])],[(0,[z1,z2,z3,z1895,z8,z6]),(0,[z1,z2,z196,z3,z42,z6]),(0,[z1,z2,z3,z427,z34,z6])],[(0,[z1,z2,z3,z1112,z21,z6]),(0,[z1,z2,z3,z123,z41,z6]),(0,[z1,z2,z3,z1896,z5,z8]),(0,[z1,z2,z3,z5,z1782,z6]),(0,[z17,z1,z2,z1794,z5,z6]),(0,[z1,z2,z3,z8,z6,z789])],[(0,[z1,z2,z139,z3,z42,z27]),(0,[z1,z11,z2,z3,z208,z5]),(0,[z1,z2,z3,z5,z1048,z6]),(0,[z1,z2,z57,z3,z42,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 32 1024 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 440) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 440).take 450) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 890).take 442) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1332).take 444) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb4 : chunkB SB 1 ((bkA.flatten.flatten.drop 1776).take 133) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1909)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [440, 450, 442, 444, 133] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_cons pb4 (windowsG_nil pbend)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 68).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 68).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 167).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 261).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 344).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 460).take 96).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 556).take 85).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc7 : chunkOK 5 ((bkB.flatten.drop 641).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc8 : chunkOK 5 ((bkB.flatten.drop 739).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc9 : chunkOK 5 ((bkB.flatten.drop 830).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc10 : chunkOK 5 ((bkB.flatten.drop 928).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc11 : chunkOK 5 ((bkB.flatten.drop 1018).take 6).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 1024)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [68, 99, 94, 83, 116, 96, 85, 98, 91, 98, 90, 6] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_cons pc7 (windowsF_cons pc8 (windowsF_cons pc9 (windowsF_cons pc10 (windowsF_cons pc11 (windowsF_nil pcend))))))))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 32) (nb2 := 1024) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38563

theorem PEqualNP.Outside.L_meta_38563 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4272482472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4272482472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38563.solve