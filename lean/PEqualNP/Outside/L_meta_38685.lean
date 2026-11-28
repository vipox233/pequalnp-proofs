import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38685

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
  Nat.testBit (4276808392 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00015898c16315c2#64 ++ 0x400015898c16315c#64 ++ 0x3013f9f9c3e73fcf#64 ++ 0xa3013f9f9c3e73fc#64 : BitVec 256),
   (0x00e4c24363284c58#64 ++ 0x800e4c24363284c5#64 ++ 0xd1ecc64fe338ccff#64 ++ 0x7d1ecc64fe338ccf#64 : BitVec 256),
   (0x160b058c0c15b0a3#64 ++ 0x0160b058c0c15b0a#64 ++ 0xfe0f078e3c3ff0fe#64 ++ 0xefe0f078e3c3ff0f#64 : BitVec 256),
   (0x2b7007603680ea0c#64 ++ 0x02b7007603680ea0#64 ++ 0xfff007f03fc0ff0d#64 ++ 0xffff007f03fc0ff0#64 : BitVec 256),
   (0x4dbee8003bfe0000#64 ++ 0x04dbee8003bfe000#64 ++ 0x6ffff8003fff000b#64 ++ 0xf6ffff8003fff000#64 : BitVec 256),
   (0x8fdfb7ff80000000#64 ++ 0x08fdfb7ff8000000#64 ++ 0x8fffffffc0000007#64 ++ 0xf8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [12, 2]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [6, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00005810c1620540 0x400005810c162054 0x0010f871c3c00f01 0x00010f871c3c00f0

def z1 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x3013f9f9c3e73fcf 0xa3013f9f9c3e73fc

def z2 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1ecc64fe338ccff 0x7d1ecc64fe338ccf

def z3 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0f078e3c3ff0fe 0xefe0f078e3c3ff0f

def z4 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfff007f03fc0ff0d 0xffff007f03fc0ff0

def z5 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z6 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x01f0f871c0000001 0x101f0f871c000000

def z7 : W := mkw 0x0000480001620000 0x0000048000162000 0x2013f80003e7000b 0xa2013f80003e7000

def z8 : W := mkw 0x00e4ca43636a4c58 0x800e4ca43636a4c5 0xf1fffe4fe3ffccff 0xff1fffe4fe3ffccf

def z9 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z10 : W := mkw 0x4dfeea437bfe4c58 0x84dfeea437bfe4c5 0xfffffe4fffffccff 0xffffffe4fffffccf

def z11 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z12 : W := mkw 0xafffb7ffb680ea0c 0x0afffb7ffb680ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0x100001f000003f04 0x0100001f000003f0

def z14 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0x2e0f018e1c3f30f2 0x82e0f018e1c3f30f

def z15 : W := mkw 0x440a280008560000 0x0440a28000856000 0x0003380000070000 0x0000338000007000

def z16 : W := mkw 0x840b309c80000000 0x0840b309c8000000 0x0003380000000000 0x0000338000000000

def z17 : W := mkw 0x1201058c0401b0a3 0x01201058c0401b0a 0x9000078e0000f0f4 0x09000078e0000f0f

def z18 : W := mkw 0x8ddeb27380000000 0x08ddeb2738000000 0x0ffff871c0000003 0xf0ffff871c000000

def z19 : W := mkw 0x0020000032800000 0x0002000003280000 0x600000003fc00008 0x0600000003fc0000

def z20 : W := mkw 0xcffea7673a9c0000 0x0cffea7673a9c000 0xcfec06063c180000 0x5cfec06063c18000

def z21 : W := mkw 0x4dbea0003a9c0000 0x04dbea0003a9c000 0x4fec00003c180000 0x54fec00003c18000

def z22 : W := mkw 0x00c4c24341200440 0x000c4c2434120044 0x91ecc64fc3200ccf 0x791ecc64fc3200cc

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000060e0000c0f4 0x09000060e0000c0f

def z24 : W := mkw 0x8f1b35bc80000000 0x08f1b35bc8000000 0x0e1339b000000000 0x80e1339b00000000

def z25 : W := mkw 0x00c592db80000000 0x000c592db8000000 0x81ffffffc0000007 0xf81ffffffc000000

def z26 : W := mkw 0x00e4824322084818 0x800e482432208481 0xc1ec06062018c030 0x5c1ec06062018c03

def z27 : W := mkw 0x020005000400a000 0x0020005000400a00 0xfe0007803c00f00c 0xefe0007803c00f00

def z28 : W := mkw 0x8fdfb7ff8400a000 0x08fdfb7ff8400a00 0xfffffffffc00f00f 0xffffffffffc00f00

def z29 : W := mkw 0x2b1005201480a204 0x02b1005201480a20 0x2e1001b01cc03300 0x82e1001b01cc0330

def z30 : W := mkw 0x3f7b07ec3e95faaf 0x03f7b07ec3e95faa 0xffff07fe3fffffff 0xfffff07fe3ffffff

def z31 : W := mkw 0x8ffff7ffe3284c58 0x88ffff7ffe3284c5 0x8fffffffc3000c07 0xf8fffffffc3000c0

def z32 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x3003f989c02730ce 0xa3003f989c02730c

def z33 : W := mkw 0x224007600400ea0c 0x0224007600400ea0 0xb01007f003c0ff0d 0xab01007f003c0ff0

def z34 : W := mkw 0x0001109880000000 0x0000110988000000 0x0013f9f9c0000007 0xa0013f9f9c000000

def z35 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x3003f809c3e73fca 0x03003f809c3e73fc

def z36 : W := mkw 0x0000400041200440 0x0000040004120044 0xd00cc64fe338ccff 0x6d00cc64fe338ccf

def z37 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xf1fcc7ffe3f8ffff 0xff1fcc7ffe3f8fff

def z38 : W := mkw 0x8fdea76700000000 0x08fdea7670000000 0x8fec060600000000 0x58fec06060000000

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00c060e2038c0fe 0x6d00c060e2038c0f

def z40 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x2013f9f1c3c73f01 0x82013f9f1c3c73f0

def z41 : W := mkw 0x0084c00341280450 0x80084c0034128045 0x000cc00fc03800f2 0x0000cc00fc03800f

def z42 : W := mkw 0x2bf4c76377a8ee5c 0x82bf4c76377a8ee5 0xfffcc7fffff8ffff 0xffffcc7fffff8fff

def z43 : W := mkw 0x0ddea24300000000 0x00ddea2430000000 0x8ffffe4fc0000007 0xf8ffffe4fc000000

def z44 : W := mkw 0x8bd4b77380000000 0x08bd4b7738000000 0x8ff0fff1c0000005 0xf8ff0fff1c000000

def z45 : W := mkw 0x060b058c00000000 0x0060b058c0000000 0x8e0f078e00000006 0xe8e0f078e0000000

def z46 : W := mkw 0x00c4824300000000 0x000c482430000000 0xd1ecc64fe038c0ff 0x7d1ecc64fe038c0f

def z47 : W := mkw 0x402048003bfe0000 0x0402048003bfe000 0x600000003fff0008 0x0600000003fff000

def z48 : W := mkw 0xcfffffffbbfe0000 0x0cfffffffbbfe000 0xefffffffffff000f 0xfefffffffffff000

def z49 : W := mkw 0x202000003680ea0c 0x0202000003680ea0 0x701001f03fc0ff0d 0xa701001f03fc0ff0

def z50 : W := mkw 0x0001589881631182 0x4000158988163118 0x2013f9b003e7330b 0xa2013f9b003e7330

def z51 : W := mkw 0x8bd5b7ff80000000 0x08bd5b7ff8000000 0x81f0ffffc0000005 0x181f0ffffc000000

def z52 : W := mkw 0x00005810c16315c2 0x400005810c16315c 0x3010f871c3e73fc9 0x03010f871c3e73fc

def z53 : W := mkw 0x160a05040c14a021 0x0160a05040c14a02 0xfe0c07863c18f03c 0xefe0c07863c18f03

def z54 : W := mkw 0x0020400063284c58 0x80020400063284c5 0x500000002338ccf8 0x0500000002338ccf

def z55 : W := mkw 0x060b058c00011082 0x0060b058c0001108 0xbe0f078e002730ce 0xebe0f078e002730c

def z56 : W := mkw 0x44aee8003bfe0000 0x044aee8003bfe000 0x600ff8003fff000a 0x0600ff8003fff000

def z57 : W := mkw 0x0001189880431182 0x4000118988043118 0x201339b000c73300 0x8201339b000c7330

def z58 : W := mkw 0x160a05040c14a021 0x0160a05040c14a02 0xee0f06063c3fc03a 0xeee0f06063c3fc03

def z59 : W := mkw 0x402048007bfe4c58 0x8402048007bfe4c5 0x700000003fffccf8 0x0700000003fffccf

def z60 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1e0c641e300cc0d 0x7d1e0c641e300cc0

def z61 : W := mkw 0x0930000032800000 0x0093000003280000 0x7ff001f03fc03f0d 0xf7ff001f03fc03f0

def z62 : W := mkw 0x4dbff898fbff15c2 0x44dbff898fbff15c 0x7ffff9f9ffff3fcf 0xf7ffff9f9ffff3fc

def z63 : W := mkw 0x8ffff7ffe3284c58 0x88ffff7ffe3284c5 0xdfffffffe338ccff 0xfdfffffffe338ccf

def z64 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00c06062018c030 0x4c00c06062018c03

def z65 : W := mkw 0x4d1b7898d9f715c2 0x44d1b7898d9f715c 0x3e13f9f9dfe73fcf 0xa3e13f9f9dfe73fc

def z66 : W := mkw 0x00c4824300000000 0x000c482430000000 0x81ecc64fc0000007 0x781ecc64fc000000

def z67 : W := mkw 0x0d9ea00000000000 0x00d9ea0000000000 0x0ffff80000000003 0xf0ffff8000000000

def z68 : W := mkw 0x00015098c1200440 0x000015098c120044 0x1013f9f9c3200ccf 0xa1013f9f9c3200cc

def z69 : W := mkw 0x2b5007601480a204 0x02b5007601480a20 0xaff007f01cc03305 0xfaff007f01cc0330

def z70 : W := mkw 0x2970026032804a0c 0x02970026032804a0 0x01f0007003c00f01 0x101f0007003c00f0

def z71 : W := mkw 0x4dbee80033ea0000 0x04dbee80033ea000 0x0ffff80003c00003 0xf0ffff80003c0000

def z72 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0x01e0c041c3000c01 0x101e0c041c3000c0

def z73 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0x2e0301801c073000 0x82e0301801c07300

def z74 : W := mkw 0x2b3005203680ea0c 0x02b3005203680ea0 0x7e1001b03fc0ff08 0x87e1001b03fc0ff0

def z75 : W := mkw 0x00e5dadbe36b5dda 0xc00e5dadbe36b5dd 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z76 : W := mkw 0x00e4824322084818 0x800e482432208481 0xc1ecc64fe018c037 0x7c1ecc64fe018c03

def z77 : W := mkw 0x0000000340000450 0x8000000034000045 0x0000000fc00000f0 0x00000000fc00000f

def z78 : W := mkw 0x140b008c081510a3 0x0140b008c081510a 0x000f000e003f00f2 0x0000f000e003f00f

def z79 : W := mkw 0x86cfb7ff80000000 0x086cfb7ff8000000 0x800fffffc0000006 0x0800fffffc000000

def z80 : W := mkw 0x202000003680ea0c 0x0202000003680ea0 0x400000003c00c000 0x0400000003c00c00

def z81 : W := mkw 0x0060024022004808 0x0006002402200480 0xd1e006402300cc0d 0x7d1e006402300cc0

def z82 : W := mkw 0x29715af8f3e35fce 0x429715af8f3e35fc 0x31f3f9f9c3e73fcf 0xb31f3f9f9c3e73fc

def z83 : W := mkw 0x00011098c00115c2 0x400011098c00115c 0x300301f9c0273fce 0xa300301f9c0273fc

def z84 : W := mkw 0xafdfb7ff8400ea0c 0x0afdfb7ff8400ea0 0x9fffffffc000ff07 0xf9fffffffc000ff0

def z85 : W := mkw 0x0060424063204c48 0x00060424063204c4 0xd1e0c649e320cccf 0x7d1e0c649e320ccc

def z86 : W := mkw 0xdfffffffbfffb0a3 0x0dfffffffbfffb0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z87 : W := mkw 0x2b7117f8b680ea0c 0x02b7117f8b680ea0 0xfff3fff9ffc0ff0f 0xffff3fff9ffc0ff0

def z88 : W := mkw 0x04aec0002b3c0000 0x004aec0002b3c000 0x6fefc0003f3f000b 0xf6fefc0003f3f000

def z89 : W := mkw 0x848fb09f80000000 0x0848fb09f8000000 0x000ff80fc0000002 0x0000ff80fc000000

def z90 : W := mkw 0x8fdea76700000000 0x08fdea7670000000 0x8ffc07f600000005 0xf8ffc07f60000000

def z91 : W := mkw 0x4dbee8007bff15c2 0x44dbee8007bff15c 0x7ffff8003fff3fcb 0xf7ffff8003fff3fc

def z92 : W := mkw 0xaffea7673680ea0c 0x0affea7673680ea0 0xcfec06063c00c000 0x5cfec06063c00c00

def z93 : W := mkw 0x493048003bfe0000 0x0493048003bfe000 0x6ff000003fff0009 0xf6ff000003fff000

def z94 : W := mkw 0x6b704f603ffeea0c 0x06b704f603ffeea0 0xfff007f03fffff0d 0xffff007f03fffff0

def z95 : W := mkw 0x0b5117f880000000 0x00b5117f88000000 0x8ff3fff9c0000007 0xf8ff3fff9c000000

def z96 : W := mkw 0x2b715ff8f7e3ffce 0x42b715ff8f7e3ffc 0xfff3fff9ffe7ffcf 0xffff3fff9ffe7ffc

def z97 : W := mkw 0x140b008c081510a3 0x0140b008c081510a 0x0003000000070000 0x0000300000007000

def z98 : W := mkw 0x00a4c00023280000 0x000a4c0002328000 0x41ecc0002338000b 0x741ecc0002338000

def z99 : W := mkw 0x8fdfffffc16315c2 0x48fdfffffc16315c 0x8fffffffc02700c7 0xf8fffffffc02700c

def z100 : W := mkw 0x1201058c0401b0a3 0x01201058c0401b0a 0xd00c078e2038f0fe 0x6d00c078e2038f0f

def z101 : W := mkw 0x297002603680ea0c 0x0297002603680ea0 0x71f000703fc0ff09 0x171f000703fc0ff0

def z102 : W := mkw 0x2020000032804a0c 0x02020000032804a0 0x0000000003c00f00 0x00000000003c00f0

def z103 : W := mkw 0x160a05040c14a021 0x0160a05040c14a02 0xde0c060e3c38c0fe 0x6de0c060e3c38c0f

def z104 : W := mkw 0x00e5d2dbe3295dda 0xc00e5d2dbe3295dd 0xd1ecc7ffe338ffff 0x7d1ecc7ffe338fff

def z105 : W := mkw 0x0b50076000000000 0x00b5007600000000 0x8ff007f000000005 0xf8ff007f00000000

def z106 : W := mkw 0x0000400041200440 0x0000040004120044 0x1000c049c3200ccf 0x21000c049c3200cc

def z107 : W := mkw 0x160b5d9ccd77b5e3 0x4160b5d9ccd77b5e 0xfe1fffffffffffff 0xefe1ffffffffffff

def z108 : W := mkw 0x3f7b5ffcfff7ffef 0x43f7b5ffcfff7ffe 0xffffffffffffffff 0xffffffffffffffff

def z109 : W := mkw 0x6ffeef603ffeea0c 0x06ffeef603ffeea0 0xfffffff03fffff0f 0xffffffff03fffff0

def z110 : W := mkw 0x00014888416315c2 0x400014888416315c 0x3003018803e73fce 0xa3003018803e73fc

def z111 : W := mkw 0x0001008800011082 0x0000100880001108 0x00030008002700c2 0x000030008002700c

def z112 : W := mkw 0x0084c00341280450 0x80084c0034128045 0x0000c001c0000000 0x00000c001c000000

def z113 : W := mkw 0x5fbfed8c3fffb0a3 0x05fbfed8c3fffb0a 0xffffff8e3ffff0ff 0xfffffff8e3ffff0f

def z114 : W := mkw 0x00a4c00363280450 0x800a4c0036328045 0x41ecc00fe33800fb 0x741ecc00fe33800f

def z115 : W := mkw 0x00a4c00363284c58 0x800a4c00363284c5 0x500cc00fe338ccfa 0x0500cc00fe338ccf

def z116 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xcfe006003c00c000 0x5cfe006003c00c00

def z117 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0x2ff001f01fc03f01 0x92ff001f01fc03f0

def z118 : W := mkw 0x8084b01380000000 0x08084b0138000000 0x0000f801c0000000 0x00000f801c000000

def z119 : W := mkw 0x040b5898c97715c2 0x4040b5898c97715c 0x7e1ff9f9ffff3fcf 0xe7e1ff9f9ffff3fc

def z120 : W := mkw 0x00a4c00023280000 0x000a4c0002328000 0xd1ecc60e2338c0ff 0x7d1ecc60e2338c0f

def z121 : W := mkw 0x00004800416315c2 0x400004800416315c 0x301001f003e73fcd 0xa301001f003e73fc

def z122 : W := mkw 0x00e4824362084c58 0x800e4824362084c5 0xd1ec064fe018ccf4 0x5d1ec064fe018ccf

def z123 : W := mkw 0x160a05040c15b0a3 0x0160a05040c15b0a 0xfe0c06063c3ff0f8 0x4fe0c06063c3ff0f

def z124 : W := mkw 0x0000000008140000 0x0000000000814000 0x600000003c3f0008 0x0600000003c3f000

def z125 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0x900f078e003ff0f6 0x0900f078e003ff0f

def z126 : W := mkw 0x00e5c2cb63295cda 0x800e5c2cb63295cd 0xf1efc7cfe33ffcff 0xff1efc7cfe33ffcf

def z127 : W := mkw 0x0060024022004808 0x0006002402200480 0x01e0004003000c01 0x101e0004003000c0

def z128 : W := mkw 0xcfbffdbcbbfe0000 0x0cfbffdbcbbfe000 0x6ffff9b03fff000b 0xf6ffff9b03fff000

def z129 : W := mkw 0x29f4c26373a84e5c 0x829f4c26373a84e5 0xd1fcc67fe3f8cfff 0x7d1fcc67fe3f8cff

def z130 : W := mkw 0x202000003680ea0c 0x0202000003680ea0 0x700000003fc0ff08 0x0700000003fc0ff0

def z131 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xdfffffffe038c0ff 0xfdfffffffe038c0f

def z132 : W := mkw 0x44aee8002b7e0000 0x044aee8002b7e000 0x41eff800233f000b 0x741eff800233f000

def z133 : W := mkw 0x49b4e80033ea0000 0x049b4e80033ea000 0x01f0f80003c00001 0x101f0f80003c0000

def z134 : W := mkw 0x4dbea8003ade0000 0x04dbea8003ade000 0x6fff38003cdf0000 0xd6fff38003cdf000

def z135 : W := mkw 0x00011098c00115c2 0x400011098c00115c 0x00000009c00000c0 0x000000009c00000c

def z136 : W := mkw 0x16efc7cf6f3dfcfb 0x816efc7cf6f3dfcf 0xffefc7cfff3ffcff 0xfffefc7cfff3ffcf

def z137 : W := mkw 0x9fdfb7ff8401b0a3 0x09fdfb7ff8401b0a 0x9fffffffc000f0f7 0xf9fffffffc000f0f

def z138 : W := mkw 0x00011098c00115c2 0x400011098c00115c 0x100001f9c0003fc4 0x0100001f9c0003fc

def z139 : W := mkw 0x00e4c24323280000 0x000e4c2432328000 0xc1ecc64fe338000f 0x7c1ecc64fe338000

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x301001f003c03f0d 0xa301001f003c03f0

def z141 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x0003f809c02700c2 0x00003f809c02700c

def z142 : W := mkw 0x448ee800097e0000 0x0448ee800097e000 0x000ff800003f0002 0x0000ff800003f000

def z143 : W := mkw 0x8fdfffff81620000 0x08fdfffff8162000 0xafffffffc3e7000f 0xfafffffffc3e7000

def z144 : W := mkw 0x4d1a280018d60000 0x04d1a280018d6000 0x2e1338001cc70000 0x82e1338001cc7000

def z145 : W := mkw 0x824117ff80000000 0x0824117ff8000000 0x800007ffc0000004 0x0800007ffc000000

def z146 : W := mkw 0x040a000008140000 0x0040a00000814000 0x000f0000003f0002 0x0000f0000003f000

def z147 : W := mkw 0x6dfeea603bfe4a0c 0x06dfeea603bfe4a0 0x6ffff8703fff0f0b 0xf6ffff8703fff0f0

def z148 : W := mkw 0x2b7107e83681fa8e 0x02b7107e83681fa8 0xfff307f83fe7ffcf 0xffff307f83fe7ffc

def z149 : W := mkw 0x8fdfb7ff88140000 0x08fdfb7ff8814000 0xeffffffffc3f000f 0xfeffffffffc3f000

def z150 : W := mkw 0x0d9ea00008140000 0x00d9ea0000814000 0x6ffff8003c3f000b 0xf6ffff8003c3f000

def z151 : W := mkw 0x0dfee24363284c58 0x80dfee24363284c5 0xdffffe4fe338ccff 0xfdffffe4fe338ccf

def z152 : W := mkw 0x224117f8c401ffce 0x4224117f8c401ffc 0x900007f9c000ffc4 0x0900007f9c000ffc

def z153 : W := mkw 0x2bf4c76377a8ee5c 0x82bf4c76377a8ee5 0xfff0c7f1ffc0ff0d 0xffff0c7f1ffc0ff0

def z154 : W := mkw 0x2b704f6037e2ea0c 0x02b704f6037e2ea0 0xfff3fff03fe7ff0f 0xffff3fff03fe7ff0

def z155 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfffc07fe3ff8ffff 0xffffc07fe3ff8fff

def z156 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x0013f879c3e70fc3 0x00013f879c3e70fc

def z157 : W := mkw 0x9fdfb7ff881510a3 0x09fdfb7ff881510a 0x8fffffffc03f00f7 0xf8fffffffc03f00f

def z158 : W := mkw 0x868fb59f80000000 0x0868fb59f8000000 0x8e0fff8fc0000006 0xe8e0fff8fc000000

def z159 : W := mkw 0x00e4da53e36a4d58 0xc00e4da53e36a4d5 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z160 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe1f07fe3fffffff 0xefe1f07fe3ffffff

def z161 : W := mkw 0x6ffea7603e9cea0c 0x06ffea7603e9cea0 0xfffc07f03fd8ff0d 0xffffc07f03fd8ff0

def z162 : W := mkw 0x100100880c15b0a3 0x0100100880c15b0a 0x700301883c3ff0fe 0xa700301883c3ff0f

def z163 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x81fcfe7fc0000007 0x781fcfe7fc000000

def z164 : W := mkw 0x2040026000004a0c 0x02040026000004a0 0x0000007000000f00 0x00000007000000f0

def z165 : W := mkw 0x49f4ea4373ea4c58 0x849f4ea4373ea4c5 0xd1fcfe4fe3f8ccff 0x7d1fcfe4fe3f8ccf

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z167 : W := mkw 0x924117ff8401b0a3 0x0924117ff8401b0a 0x900007ffc000f0f4 0x0900007ffc000f0f

def z168 : W := mkw 0x160b058c0401b0a3 0x0160b058c0401b0a 0x9e0f078e0000f0f6 0xe9e0f078e0000f0f

def z169 : W := mkw 0x0001189880431182 0x4000118988043118 0x0003380000070000 0x0000338000007000

def z170 : W := mkw 0x4dbee8037bfe0450 0x84dbee8037bfe045 0x6ffff80fffff00fb 0xf6ffff80fffff00f

def z171 : W := mkw 0x4dbee8007bfe0440 0x04dbee8007bfe044 0x7ffff849ffff0ccf 0xf7ffff849ffff0cc

def z172 : W := mkw 0x2970026032804a0c 0x02970026032804a0 0x01e0000000000000 0x101e000000000000

def z173 : W := mkw 0x8d9fb09f80000000 0x08d9fb09f8000000 0x0ffff80fc0000003 0xf0ffff80fc000000

def z174 : W := mkw 0x0930480033e20000 0x00930480033e2000 0x6ff3f8003fe7000b 0xf6ff3f8003fe7000

def z175 : W := mkw 0x06cf87cf00000000 0x006cf87cf0000000 0x8fefc7cfc0000007 0xf8fefc7cfc000000

def z176 : W := mkw 0x140b008c0c15b0a3 0x0140b008c0c15b0a 0x700f000e3c3ff0fa 0x0700f000e3c3ff0f

def z177 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c049c0000007 0x20000c049c000000

def z178 : W := mkw 0x140b008c081510a3 0x0140b008c081510a 0x300f018e003f30fe 0xa300f018e003f30f

def z179 : W := mkw 0x040a000008140000 0x0040a00000814000 0x6e0f00003c3f000a 0xe6e0f00003c3f000

def z180 : W := mkw 0x026007402600e808 0x0026007402600e80 0xffe007c03f00fc0d 0xfffe007c03f00fc0

def z181 : W := mkw 0x0910000010800000 0x0091000001080000 0x2e1000001cc00000 0x82e1000001cc0000

def z182 : W := mkw 0x4d9ea80018d60000 0x04d9ea80018d6000 0x2ffff8001cc70003 0xf2ffff8001cc7000

def z183 : W := mkw 0x448ee800097e0000 0x0448ee800097e000 0x6e0ff8003c3f000a 0xe6e0ff8003c3f000

def z184 : W := mkw 0x060b058c0400a000 0x0060b058c0400a00 0xfe0f078e3c00f00e 0xefe0f078e3c00f00

def z185 : W := mkw 0x0001008800011082 0x0000100880001108 0x30030188002730ce 0xa30030188002730c

def z186 : W := mkw 0x4d3a28003ad60000 0x04d3a28003ad6000 0x6ff338003fc70009 0xf6ff338003fc7000

def z187 : W := mkw 0x0f5b07ec00000000 0x00f5b07ec0000000 0x8fff07fe00000007 0xf8fff07fe0000000

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000004003000c0d 0x21000004003000c0

def z189 : W := mkw 0x02e4c7436728ec58 0x802e4c7436728ec5 0xffecc7cfff38fcff 0xfffecc7cfff38fcf

def z190 : W := mkw 0x0000181080420100 0x4000018108042010 0x0010383000c00300 0x00010383000c0030

def z191 : W := mkw 0x060b058c00000000 0x0060b058c0000000 0x0e03018000000000 0x80e0301800000000

def z192 : W := mkw 0x40004800097e0000 0x040004800097e000 0x00000000003f0000 0x000000000003f000

def z193 : W := mkw 0x00c4824300000000 0x000c482430000000 0x81ec060600000000 0x581ec06060000000

def z194 : W := mkw 0x8f1b7dbcc16315c2 0x48f1b7dbcc16315c 0x3e13f9f9c3e73fcf 0xa3e13f9f9c3e73fc

def z195 : W := mkw 0x82415fffc16315c2 0x482415fffc16315c 0xb013ffffc3e73fcf 0xab013ffffc3e73fc

def z196 : W := mkw 0x2b7007637680ee5c 0x82b7007637680ee5 0xfff007ffffc0fffd 0xffff007ffffc0fff

def z197 : W := mkw 0x8fdeb77780000000 0x08fdeb7778000000 0x8ffcfe77c0000001 0x58ffcfe77c000000

def z198 : W := mkw 0x00e4824322084818 0x800e482432208481 0xd1ec060e2038c0fe 0x7d1ec060e2038c0f

def z199 : W := mkw 0x160a05040c14a021 0x0160a05040c14a02 0xce0c06063c18c030 0x4ce0c06063c18c03

def z200 : W := mkw 0x9fdfb7ff8c14a021 0x09fdfb7ff8c14a02 0xcffffffffc18c037 0xfcffffffffc18c03

def z201 : W := mkw 0x0040024340004c58 0x80040024340004c5 0x00000041c0000c00 0x000000041c0000c0

def z202 : W := mkw 0x84cfb2df80000000 0x084cfb2df8000000 0x81effe4fc0000007 0x781effe4fc000000

def z203 : W := mkw 0x100000000c15b0a3 0x0100000000c15b0a 0xf00c060e3c3ff0fe 0x6f00c060e3c3ff0f

def z204 : W := mkw 0x40e4ca437bfe4c58 0x840e4ca437bfe4c5 0xf1ecc64fffffccff 0x7f1ecc64fffffccf

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x2010000003c00009 0xa2010000003c0000

def z206 : W := mkw 0x0040024000000000 0x0004002400000000 0x81e0064000000005 0x781e006400000000

def z207 : W := mkw 0x0b5007600400a000 0x00b5007600400a00 0xfff007f03c00f00d 0xffff007f03c00f00

def z208 : W := mkw 0x0bf4c76363284c58 0x80bf4c76363284c5 0xdffcc7ffe338ccff 0xfdffcc7ffe338ccf

def z209 : W := mkw 0x824117ff80000000 0x0824117ff8000000 0x8013ffffc0000007 0xa8013ffffc000000

def z210 : W := mkw 0x8fdfffffc16315c2 0x48fdfffffc16315c 0xbfffffffc3e73fcf 0xfbfffffffc3e73fc

def z211 : W := mkw 0x00c5dadbc16315c2 0x400c5dadbc16315c 0xb1ffffffc3e73fcf 0xfb1ffffffc3e73fc

def z212 : W := mkw 0x020005000400a000 0x0020005000400a00 0xce0006003c00c000 0x4ce0006003c00c00

def z213 : W := mkw 0x848fb09f80000000 0x0848fb09f8000000 0x001ff9ffc0000007 0xa001ff9ffc000000

def z214 : W := mkw 0x00011898c04315c2 0x400011898c04315c 0x301339f9c0c73fc4 0x8301339f9c0c73fc

def z215 : W := mkw 0x10000000081510a3 0x010000000081510a 0x00000000003f00f0 0x000000000003f00f

def z216 : W := mkw 0x0000480041620440 0x0000048004162044 0x3013f849c3e70ccf 0xa3013f849c3e70cc

def z217 : W := mkw 0x0200050000000000 0x0020005000000000 0x8e00078000000004 0xe8e0007800000000

def z218 : W := mkw 0x0040024340004c58 0x80040024340004c5 0x9000064fc000ccf4 0x09000064fc000ccf

def z219 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xbfffffffc3c03f0f 0xfbfffffffc3c03f0

def z220 : W := mkw 0x49b4f810f3ea0540 0x449b4f810f3ea054 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z221 : W := mkw 0x00004800416315c2 0x400004800416315c 0x3000000003e73fc8 0x03000000003e73fc

def z222 : W := mkw 0x224007634400ee5c 0x8224007634400ee5 0x900007ffc000fff4 0x0900007ffc000fff

def z223 : W := mkw 0x206002403680ea0c 0x0206002403680ea0 0xf1e006403fc0ff0d 0x7f1e006403fc0ff0

def z224 : W := mkw 0x00c4824340004c58 0x800c4824340004c5 0x91ecc64fc000ccf7 0x791ecc64fc000ccf

def z225 : W := mkw 0x8ffea76722084818 0x88ffea7672208481 0xcfec06062018c030 0x5cfec06062018c03

def z226 : W := mkw 0x89d5fafbc16315c2 0x489d5fafbc16315c 0x31f3f9f9c3e73fcf 0xb31f3f9f9c3e73fc

def z227 : W := mkw 0x160b1d9c8c57b1a3 0x4160b1d9c8c57b1a 0x2e1339b01cc73300 0x82e1339b01cc7330

def z228 : W := mkw 0x060a050400000000 0x0060a05040000000 0x8e0c060600000000 0x48e0c06060000000

def z229 : W := mkw 0x4d1a280018d60000 0x04d1a280018d6000 0x6e1f38003cff000a 0xe6e1f38003cff000

def z230 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0x91f007f003c0ff05 0x191f007f003c0ff0

def z231 : W := mkw 0x0000000040004c58 0x80000000040004c5 0x100000000000ccf0 0x0100000000000ccf

def z232 : W := mkw 0x4fbfed8c3bfe0000 0x04fbfed8c3bfe000 0xefffff8e3fff000f 0xfefffff8e3fff000

def z233 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0x3e0301881c2730ce 0xa3e0301881c2730c

def z234 : W := mkw 0x0084800000000000 0x0008480000000000 0x01ecc00000000003 0x701ecc0000000000

def z235 : W := mkw 0x22415ff8c563ffce 0x422415ff8c563ffc 0xb013fff9c3e7ffcf 0xab013fff9c3e7ffc

def z236 : W := mkw 0x964b17ff8c15b0a3 0x0964b17ff8c15b0a 0xfe0f07fffc3ff0fe 0xefe0f07fffc3ff0f

def z237 : W := mkw 0x89d5b2fb80000000 0x089d5b2fb8000000 0x01f3f9f9c0000007 0xb01f3f9f9c000000

def z238 : W := mkw 0x9ffff7ffef3dfcfb 0x89ffff7ffef3dfcf 0xffffffffff3ffcff 0xfffffffffff3ffcf

def z239 : W := mkw 0x4dfea2433a9c4818 0x84dfea2433a9c481 0xcfec06063c18c030 0x5cfec06063c18c03

def z240 : W := mkw 0x12e5c7cf6729fcfb 0x812e5c7cf6729fcf 0xd1ecc7cfe338fcff 0x7d1ecc7cfe338fcf

def z241 : W := mkw 0xbfffb7ffbe95faaf 0x0bfffb7ffbe95faa 0xffffffffffffffff 0xffffffffffffffff

def z242 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x1003f9f9c0273fc6 0x01003f9f9c0273fc

def z243 : W := mkw 0x1201058c0401b0a3 0x01201058c0401b0a 0xfe00078e3c00f0fc 0xefe00078e3c00f0f

def z244 : W := mkw 0xafdfb7ff9480a204 0x0afdfb7ff9480a20 0xafffffffdcc03307 0xfafffffffdcc0330

def z245 : W := mkw 0x4fbeed003ffea000 0x04fbeed003ffea00 0xffffff803ffff00f 0xfffffff803ffff00

def z246 : W := mkw 0x2bf5dffbf7ebffde 0xc2bf5dffbf7ebffd 0xffffffffffffffff 0xffffffffffffffff

def z247 : W := mkw 0x8040127380000000 0x0804012738000000 0x00000071c0000000 0x000000071c000000

def z248 : W := mkw 0x226007603680ea0c 0x0226007603680ea0 0xf00007f03fc0ff0c 0x0f00007f03fc0ff0

def z249 : W := mkw 0x100000000c15b0a3 0x0100000000c15b0a 0x700000003c3ff0f8 0x0700000003c3ff0f

def z250 : W := mkw 0x5f1b2d8c1cd7b0a3 0x05f1b2d8c1cd7b0a 0xfe1f3f8e3cfff0fe 0xefe1f3f8e3cfff0f

def z251 : W := mkw 0x00615ad8e3635dca 0x400615ad8e3635dc 0xf1f3fff9e3e7ffcf 0xff1f3fff9e3e7ffc

def z252 : W := mkw 0x6ffeef637ffeee5c 0x86ffeef637ffeee5 0xffffffffffffffff 0xffffffffffffffff

def z253 : W := mkw 0x0000000000011082 0x0000000000001108 0x30000000002730c8 0x030000000002730c

def z254 : W := mkw 0x0994a00000000000 0x00994a0000000000 0x01f0f80000000001 0x101f0f8000000000

def z255 : W := mkw 0x048ea00000000000 0x0048ea0000000000 0x000ff80000000002 0x0000ff8000000000

def z256 : W := mkw 0x9f1b35bc8c15b0a3 0x09f1b35bc8c15b0a 0xfe1f3fbe3c3ff0fe 0xefe1f3fbe3c3ff0f

def z257 : W := mkw 0x29705a70f3e24f4c 0x429705a70f3e24f4 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z258 : W := mkw 0x160b159c8c15b0a3 0x0160b159c8c15b0a 0xfe1ffffffc3ff0ff 0xefe1ffffffc3ff0f

def z259 : W := mkw 0x2b1005201480a204 0x02b1005201480a20 0xfe1007b03cc0f30c 0xefe1007b03cc0f30

def z260 : W := mkw 0x7fffefec3ffffaaf 0x07fffefec3ffffaa 0xfffffffe3fffffff 0xffffffffe3ffffff

def z261 : W := mkw 0x6f1a2d201cd6a204 0x06f1a2d201cd6a20 0x2e1339b01cc73300 0x82e1339b01cc7330

def z262 : W := mkw 0x0001008800011082 0x0000100880001108 0x2003018000073000 0x8200301800007300

def z263 : W := mkw 0x448ee800097e0000 0x0448ee800097e000 0x201ff80003ff000b 0xa201ff80003ff000

def z264 : W := mkw 0x0000400041200440 0x0000040004120044 0x3010c1f9c3e03fcf 0xa3010c1f9c3e03fc

def z265 : W := mkw 0xa24117ff8400ea0c 0x0a24117ff8400ea0 0x900007ffc000ff04 0x0900007ffc000ff0

def z266 : W := mkw 0x00005810c1620540 0x400005810c162054 0x0000f801c0000000 0x00000f801c000000

def z267 : W := mkw 0x864b17ff80000000 0x0864b17ff8000000 0x8e0f07ffc0000006 0xe8e0f07ffc000000

def z268 : W := mkw 0x224007600400ea0c 0x0224007600400ea0 0x900007f00000ff04 0x0900007f00000ff0

def z269 : W := mkw 0x1f5b07ec0c15b0a3 0x01f5b07ec0c15b0a 0xffff07fe3c3ff0ff 0xfffff07fe3c3ff0f

def z270 : W := mkw 0x0020000022084818 0x8002000002208481 0x400000002018c030 0x0400000002018c03

def z271 : W := mkw 0x040a000008140000 0x0040a00000814000 0x2e0300001c070000 0x82e0300001c07000

def z272 : W := mkw 0x020005000400a000 0x0020005000400a00 0xfe0c078e3c38f0fe 0xefe0c078e3c38f0f

def z273 : W := mkw 0x8fdfb7ffc0004c58 0x88fdfb7ffc0004c5 0x9fffffffc000ccf7 0xf9fffffffc000ccf

def z274 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0x51e0c041e338ccf9 0x151e0c041e338ccf

def z275 : W := mkw 0x293000003680ea0c 0x0293000003680ea0 0x7ff000003fc0ff09 0xf7ff000003fc0ff0

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0x201001b000c03300 0x8201001b000c0330

def z277 : W := mkw 0x402048007bff15c2 0x4402048007bff15c 0x700000003fff3fc8 0x0700000003fff3fc

def z278 : W := mkw 0x4dfee2437bbc4c58 0x84dfee2437bbc4c5 0xdfecc64fff38ccff 0x7dfecc64fff38ccf

def z279 : W := mkw 0x0dbea00032800000 0x00dbea0003280000 0x6ffff8003fc0000b 0xf6ffff8003fc0000

def z280 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0x81ecc64fc3000c07 0x781ecc64fc3000c0

def z281 : W := mkw 0x0930000032800000 0x0093000003280000 0x6ff000003fc00009 0xf6ff000003fc0000

def z282 : W := mkw 0x00e4c24323284818 0x800e4c2432328481 0xc1ecc6062338c03b 0x7c1ecc6062338c03

def z283 : W := mkw 0x220005200400a204 0x0220005200400a20 0x000001b000003300 0x0000001b00000330

def z284 : W := mkw 0x0930000032800000 0x0093000003280000 0x01f0000003c00001 0x101f0000003c0000

def z285 : W := mkw 0xab7117ffb680ea0c 0x0ab7117ffb680ea0 0xfff007ffffc0ff0d 0xffff007ffffc0ff0

def z286 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8fec07ffc0000004 0x58fec07ffc000000

def z287 : W := mkw 0x6bf4ef6037eaea0c 0x06bf4ef6037eaea0 0xfff0fff03fc0ff0d 0xffff0fff03fc0ff0

def z288 : W := mkw 0x00001010c0000540 0x400001010c000054 0x00000071c0000f00 0x000000071c0000f0

def z289 : W := mkw 0x16afc58c2f3db0a3 0x016afc58c2f3db0a 0xffefc78e3f3ff0ff 0xfffefc78e3f3ff0f

def z290 : W := mkw 0x160b5d9ccd77b5e3 0x4160b5d9ccd77b5e 0xfe0fff8ffc3ff0fe 0xefe0fff8ffc3ff0f

def z291 : W := mkw 0x224007600400ea0c 0x0224007600400ea0 0x800006000000c000 0x0800006000000c00

def z292 : W := mkw 0x8f5b37fc80000000 0x08f5b37fc8000000 0x8ff33ff000000005 0xf8ff33ff00000000

def z293 : W := mkw 0x0084c00341280450 0x80084c0034128045 0x100cc04fc3380cff 0x2100cc04fc3380cf

def z294 : W := mkw 0x0001109880000000 0x0000110988000000 0x000001f9c0000004 0x0000001f9c000000

def z295 : W := mkw 0x402000003a9c0000 0x0402000003a9c000 0x400000003c180000 0x0400000003c18000

def z296 : W := mkw 0x100000000c14a021 0x0100000000c14a02 0x400000003c18c030 0x0400000003c18c03

def z297 : W := mkw 0x8ffff7ffa3280000 0x08ffff7ffa328000 0xcfffffffe338000f 0xfcfffffffe338000

def z298 : W := mkw 0x4dbee8007bfe4c58 0x84dbee8007bfe4c5 0x7ffff8003fffccfb 0xf7ffff8003fffccf

def z299 : W := mkw 0x160b4d8c0d77b0a3 0x0160b4d8c0d77b0a 0xfe1fff8e3ffff0ff 0xefe1fff8e3ffff0f

def z300 : W := mkw 0x8910303080000000 0x0891030308000000 0x0010383000000000 0x0001038300000000

def z301 : W := mkw 0x2b70476077a8ee5c 0x82b70476077a8ee5 0xfff007f03ff8fffd 0xffff007f03ff8fff

def z302 : W := mkw 0x968fb59f8c15b0a3 0x0968fb59f8c15b0a 0xfe0fff8ffc3ff0fe 0xefe0fff8ffc3ff0f

def z303 : W := mkw 0x8fdfb7ff80011082 0x08fdfb7ff8001108 0xbfffffffc02730cf 0xfbfffffffc02730c

def z304 : W := mkw 0x49b4a00032880000 0x049b4a0003288000 0x01e0000000000000 0x101e000000000000

def z305 : W := mkw 0x8ffee76763284c58 0x88ffee76763284c5 0xdfecc64fe338ccff 0x7dfecc64fe338ccf

def z306 : W := mkw 0x448ff898c97f15c2 0x4448ff898c97f15c 0x301ff9f9c3ff3fcf 0xa301ff9f9c3ff3fc

def z307 : W := mkw 0x0060424363284c58 0x80060424363284c5 0xd000064fe338ccfc 0x0d000064fe338ccf

def z308 : W := mkw 0x6ffffff8ffffffce 0x46ffffff8ffffffc 0xfffffff9ffffffcf 0xffffffff9ffffffc

def z309 : W := mkw 0x0001109880011082 0x0000110988001108 0x3013f9f9c02730cf 0xa3013f9f9c02730c

def z310 : W := mkw 0x10e4c2436f3dfcfb 0x810e4c2436f3dfcf 0xf1ecc64fff3ffcff 0x7f1ecc64fff3ffcf

def z311 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8fff3fb600000000 0xd8fff3fb60000000

def z312 : W := mkw 0x040a480009760000 0x0040a48000976000 0x6e1ff8003fff000b 0xe6e1ff8003fff000

def z313 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x0ff3f9f1c0000001 0x90ff3f9f1c000000

def z314 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xde0c078e3c18f0f4 0x4de0c078e3c18f0f

def z315 : W := mkw 0x2b3005203680a204 0x02b3005203680a20 0x6ff001b03fc03309 0xf6ff001b03fc0330

def z316 : W := mkw 0x0000480041620540 0x4000048004162054 0x0000000003c00f00 0x00000000003c00f0

def z317 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xce0f060e3c3fc0f2 0x4ce0f060e3c3fc0f

def z318 : W := mkw 0x148fc08f493d14f3 0x8148fc08f493d14f 0x000fc00fc03f00f2 0x0000fc00fc03f00f

def z319 : W := mkw 0x200000001480a204 0x0200000001480a20 0x200000001cc03300 0x0200000001cc0330

def z320 : W := mkw 0x0020400023280000 0x0002040002328000 0x4000000023380008 0x0400000002338000

def z321 : W := mkw 0x102040006f3dfcfb 0x8102040006f3dfcf 0x700000003f3ffcf8 0x0700000003f3ffcf

def z322 : W := mkw 0x0dbee00023280000 0x00dbee0002328000 0x4ffff8002338000b 0xf4ffff8002338000

def z323 : W := mkw 0x3f7a07643e94ea2d 0x03f7a07643e94ea2 0xfffc07f63fd8ff3d 0xffffc07f63fd8ff3

def z324 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xeff006003fc0c009 0xfeff006003fc0c00

def z325 : W := mkw 0x2b711ff8b6c3fb8e 0x42b711ff8b6c3fb8 0xfff33ff03fc7ff0d 0xffff33ff03fc7ff0

def z326 : W := mkw 0x00004800416315c2 0x400004800416315c 0x3013f80003e73fcb 0xa3013f80003e73fc

def z327 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8feffe0fc0000002 0x58feffe0fc000000

def z328 : W := mkw 0x0000080000431182 0x4000008000043118 0x2000000000c73300 0x02000000000c7330

def z329 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0xf01fffffe3ffffff 0xef01fffffe3fffff

def z330 : W := mkw 0x0001488801631082 0x0000148880163108 0x3013f98803e730cf 0xa3013f98803e730c

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000008002000ce 0x210000008002000c

def z332 : W := mkw 0x0020400063284c58 0x80020400063284c5 0x5000c049e338ccff 0x25000c049e338ccf

def z333 : W := mkw 0xaffea7673680ea0c 0x0affea7673680ea0 0xfffc07f63fc0ff0d 0xffffc07f63fc0ff0

def z334 : W := mkw 0x568fed8c0d7fb0a3 0x0568fed8c0d7fb0a 0xfe0fff8e3c3ff0fe 0xefe0fff8e3c3ff0f

def z335 : W := mkw 0x89d4fa73c1620540 0x489d4fa73c162054 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z336 : W := mkw 0x0001008800000000 0x0000100880000000 0x0003018800000006 0xa000301880000000

def z337 : W := mkw 0x12015d9cc563b5e3 0x412015d9cc563b5e 0xb013ffffc3e7ffff 0xab013ffffc3e7fff

def z338 : W := mkw 0x49f4ea4373ea4c58 0x849f4ea4373ea4c5 0x01f0f841c3c00c01 0x101f0f841c3c00c0

def z339 : W := mkw 0xcdfefa73bbfe0000 0x0cdfefa73bbfe000 0x6ffff871ffff000b 0xf6ffff871ffff000

def z340 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x4feff8003c3f0002 0x54feff8003c3f000

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0x001001f000000005 0xa001001f00000000

def z342 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0xfffffe0e3fffc0ff 0xffffffe0e3fffc0f

def z343 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x1003f849c3270ccf 0x21003f849c3270cc

def z344 : W := mkw 0x0060024362004c58 0x80060024362004c5 0xd1e0064fe300ccfd 0x7d1e0064fe300ccf

def z345 : W := mkw 0x160a05040c14a021 0x0160a05040c14a02 0x0e0000001c000000 0x00e0000001c00000

def z346 : W := mkw 0x16eec7476f3cec79 0x816eec7476f3cec7 0xdfecc64fff38ccff 0x7dfecc64fff38ccf

def z347 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xafffffffdc073007 0xfafffffffdc07300

def z348 : W := mkw 0x040a000008140000 0x0040a00000814000 0xfe0f060e3c3fc0fe 0xefe0f060e3c3fc0f

def z349 : W := mkw 0x0001008800011082 0x0000100880001108 0x301301f803e73fcf 0xa301301f803e73fc

def z350 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c00002038000a 0x6400c00002038000

def z351 : W := mkw 0x02015d98c563b5c2 0x402015d98c563b5c 0xfe13fff9ffe7ffcf 0xefe13fff9ffe7ffc

def z352 : W := mkw 0x00005810c1620540 0x400005810c162054 0x1010f879c3e00fcf 0x21010f879c3e00fc

def z353 : W := mkw 0xcffffffffbfe4c58 0x8cffffffffbfe4c5 0xffffffffffffccff 0xfffffffffffffccf

def z354 : W := mkw 0x140b589cc97715e3 0x4140b589cc97715e 0x000ff80fc03f00f2 0x0000ff80fc03f00f

def z355 : W := mkw 0x8fdfffffc1620540 0x48fdfffffc162054 0x8fffffffc3c00f07 0xf8fffffffc3c00f0

def z356 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x7ffff9f03fff3f0f 0xf7ffff9f03fff3f0

def z357 : W := mkw 0x226007602600ea0c 0x0226007602600ea0 0xd1e007f02300ff0d 0x7d1e007f02300ff0

def z358 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xeff007b03cc0f300 0xdeff007b03cc0f30

def z359 : W := mkw 0x00e4824322084818 0x800e482432208481 0xd1ec06462318cc3d 0x7d1ec06462318cc3

def z360 : W := mkw 0x5fbfed8c3fffb0a3 0x05fbfed8c3fffb0a 0x6ffff9803fff300b 0xf6ffff9803fff300

def z361 : W := mkw 0x00015898c1620540 0x400015898c162054 0x0013f9f9c3c00f07 0xa0013f9f9c3c00f0

def z362 : W := mkw 0x00011098c00115c2 0x400011098c00115c 0x301001f9c3c03fcd 0xa301001f9c3c03fc

def z363 : W := mkw 0x44eeea436b7e4c58 0x844eeea436b7e4c5 0xd1effe4fe33fccff 0x7d1effe4fe33fccf

def z364 : W := mkw 0x448ff898c97f15c2 0x4448ff898c97f15c 0x000ff809c03f00c2 0x0000ff809c03f00c

def z365 : W := mkw 0x040a000000000000 0x0040a00000000000 0x0e0f000000000002 0xe0e0f00000000000

def z366 : W := mkw 0x0910000000000000 0x0091000000000000 0x0ff0000000000001 0xf0ff000000000000

def z367 : W := mkw 0x0d3a00003a940000 0x00d3a00003a94000 0x6fff00003fff000b 0xf6fff00003fff000

def z368 : W := mkw 0x0b50076000000000 0x00b5007600000000 0x8fe0060000000000 0x58fe006000000000

def z369 : W := mkw 0x0d9ea00000000000 0x00d9ea0000000000 0x0fec000000000000 0x50fec00000000000

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x800c060e00000006 0x6800c060e0000000

def z371 : W := mkw 0x124107cf4401fcfb 0x8124107cf4401fcf 0x900007cfc000fcf4 0x0900007cfc000fcf

def z372 : W := mkw 0x4dfeea403bfe4808 0x04dfeea403bfe480 0xfffffe403fffcc0f 0xffffffe403fffcc0

def z373 : W := mkw 0x0084c00341280450 0x80084c0034128045 0xd00cc60fe038c0fe 0x6d00cc60fe038c0f

def z374 : W := mkw 0x222005003680ea0c 0x0222005003680ea0 0xfe0007803fc0ff0c 0xefe0007803fc0ff0

def z375 : W := mkw 0x060b159c80000000 0x0060b159c8000000 0x8e1fffffc0000007 0xe8e1fffffc000000

def z376 : W := mkw 0x00c4824300000000 0x000c482430000000 0x01e0c041c0000001 0x101e0c041c000000

def z377 : W := mkw 0x8b5117ff80000000 0x08b5117ff8000000 0x8ff007ffc0000005 0xf8ff007ffc000000

def z378 : W := mkw 0x848ff89fc16315c2 0x4848ff89fc16315c 0x301ff9ffc3e73fcf 0xa301ff9ffc3e73fc

def z379 : W := mkw 0x2970026032804a0c 0x02970026032804a0 0x6ff000703fc00f09 0xf6ff000703fc00f0

def z380 : W := mkw 0x00e4824322004808 0x000e482432200480 0xd1ecc64fe300cc0f 0x7d1ecc64fe300cc0

def z381 : W := mkw 0x040b008808151082 0x0040b00880815108 0x7e0f01883c3f30ce 0xe7e0f01883c3f30c

def z382 : W := mkw 0x0040024000004808 0x0004002400000480 0x900006400000cc04 0x0900006400000cc0

def z383 : W := mkw 0x16cf87cf0c15b0a3 0x016cf87cf0c15b0a 0xffefc7cffc3ff0ff 0xfffefc7cffc3ff0f

def z384 : W := mkw 0x0060024022004808 0x0006002402200480 0xd1ec064e2338ccff 0x7d1ec064e2338ccf

def z385 : W := mkw 0x9fdfa7ef0c15b0a3 0x09fdfa7ef0c15b0a 0xffef078e3c3ff0fe 0xfffef078e3c3ff0f

def z386 : W := mkw 0x166b07cc2e15f8ab 0x0166b07cc2e15f8a 0xffef07ce3f3ffcff 0xfffef07ce3f3ffcf

def z387 : W := mkw 0x0970024032804808 0x0097002403280480 0xfff006403fc0cc0d 0xffff006403fc0cc0

def z388 : W := mkw 0x4020480033ea0000 0x04020480033ea000 0x0000000003c00000 0x00000000003c0000

def z389 : W := mkw 0x0001109880011182 0x4000110988001118 0x000001b000003300 0x0000001b00000330

def z390 : W := mkw 0x3f7b07ec3e95faaf 0x03f7b07ec3e95faa 0xffef078e3c3ff0fe 0xfffef078e3c3ff0f

def z391 : W := mkw 0x0000400001200000 0x0000040000120000 0x0000c0000320000b 0x20000c0000320000

def z392 : W := mkw 0x0084800300080010 0x8008480030008001 0x000c000600180030 0x0000c00060018003

def z393 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xffe006003fc0ff08 0x5ffe006003fc0ff0

def z394 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x2ff3f8001fc70001 0x92ff3f8001fc7000

def z395 : W := mkw 0x8f5b37ff80000000 0x08f5b37ff8000000 0x8e133fffc0000004 0x88e133fffc000000

def z396 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e0000003c000008 0xe6e0000003c00000

def z397 : W := mkw 0x2020480077e3ffce 0x42020480077e3ffc 0x700000003fe7ffc8 0x0700000003fe7ffc

def z398 : W := mkw 0x82e5d7ffe3284c58 0x882e5d7ffe3284c5 0xd1ecc7ffe338ccff 0x7d1ecc7ffe338ccf

def z399 : W := mkw 0x0201058c00000000 0x00201058c0000000 0x8000078e00000004 0x08000078e0000000

def z400 : W := mkw 0x8f1a252400000000 0x08f1a25240000000 0x0e00000000000000 0x00e0000000000000

def z401 : W := mkw 0x2bf487633688ea1c 0x82bf487633688ea1 0xfffc07f63fd8ff3d 0xffffc07f63fd8ff3

def z402 : W := mkw 0x4dbfe8883bff1082 0x04dbfe8883bff108 0x7ffff9883fff30cf 0xf7ffff9883fff30c

def z403 : W := mkw 0x8240076700000000 0x0824007670000000 0x8000060600000000 0x0800006060000000

def z404 : W := mkw 0x100000000c15b0a3 0x0100000000c15b0a 0x200000001c073000 0x0200000001c07300

def z405 : W := mkw 0x4d3a68003bfe0000 0x04d3a68003bfe000 0x6e1338003fff0008 0x86e1338003fff000

def z406 : W := mkw 0x3b7107ec3681faaf 0x03b7107ec3681faa 0xfff007fe3fc0fffd 0xffff007fe3fc0fff

def z407 : W := mkw 0x4d1a200018940000 0x04d1a20001894000 0x0e0000001c000000 0x00e0000001c00000

def z408 : W := mkw 0x0085d89bc16b15d2 0xc0085d89bc16b15d 0x301ff9ffc3ff3fff 0xa301ff9ffc3ff3ff

def z409 : W := mkw 0x820115bc80000000 0x0820115bc8000000 0x000001b000000000 0x0000001b00000000

def z410 : W := mkw 0x602048003ffeea0c 0x0602048003ffeea0 0x700000003fffff08 0x0700000003fffff0

def z411 : W := mkw 0x00014088412114c2 0x000014088412114c 0x3003c1c9c3273ccf 0xa3003c1c9c3273cc

def z412 : W := mkw 0x0084800300000000 0x0008480030000000 0x000cc00fc0000002 0x0000cc00fc000000

def z413 : W := mkw 0x3f1b05ac1c95b2a7 0x03f1b05ac1c95b2a 0x2e1301b01cc73300 0x82e1301b01cc7330

def z414 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x2013f9b9c0e733c2 0x82013f9b9c0e733c

def z415 : W := mkw 0x1f9fa58c0c15b0a3 0x01f9fa58c0c15b0a 0xffffff8e3c3ff0ff 0xfffffff8e3c3ff0f

def z416 : W := mkw 0x6ffeef603ffeea0c 0x06ffeef603ffeea0 0xeffffe003fffc00b 0xfeffffe003fffc00

def z417 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x301339b003e73fc8 0x8301339b003e73fc

def z418 : W := mkw 0xcfffffffb3ea0000 0x0cfffffffb3ea000 0x8fffffffc3c00007 0xf8fffffffc3c0000

def z419 : W := mkw 0x0020400063284c58 0x80020400063284c5 0x0000000003000c00 0x00000000003000c0

def z420 : W := mkw 0x0240076000000000 0x0024007600000000 0x800007f000000004 0x0800007f00000000

def z421 : W := mkw 0x160b458c4d35b4e3 0x0160b458c4d35b4e 0xfe0fc7cfff3ffcff 0xefe0fc7cfff3ffcf

def z422 : W := mkw 0x160b1d9c8c57b1a3 0x4160b1d9c8c57b1a 0xfe1f3fbe3cfff3fe 0xefe1f3fbe3cfff3f

def z423 : W := mkw 0xaffff7fff7a8ee5c 0x8affff7fff7a8ee5 0xfffffffffff8ffff 0xffffffffffff8fff

def z424 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0x6e0f01803c3f300a 0xe6e0f01803c3f300

def z425 : W := mkw 0x6f7a2f603ed6ea0c 0x06f7a2f603ed6ea0 0xfff33ff03fc7ff0d 0xffff33ff03fc7ff0

def z426 : W := mkw 0x0040024340004c58 0x80040024340004c5 0xd00c064fe038ccfe 0x6d00c064fe038ccf

def z427 : W := mkw 0x89d4a26300000000 0x089d4a2630000000 0x01e0000000000000 0x101e000000000000

def z428 : W := mkw 0x4dbef810fbfe0540 0x44dbef810fbfe054 0x6ffff871ffff0f0b 0xf6ffff871ffff0f0

def z429 : W := mkw 0x0000480001620000 0x0000048000162000 0x2000000003e70008 0x02000000003e7000

def z430 : W := mkw 0x1001008c000110a3 0x01001008c000110a 0x0000000e000000f0 0x00000000e000000f

def z431 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xcff006703fc0cf01 0x5cff006703fc0cf0

def z432 : W := mkw 0xc9f4fa73b3ea0000 0x0c9f4fa73b3ea000 0x01f0f871c3c00001 0x101f0f871c3c0000

def z433 : W := mkw 0x0001008800011082 0x0000100880001108 0xf00f078e203ff0fe 0xef00f078e203ff0f

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x300001800000300c 0xa300001800000300

def z435 : W := mkw 0x10015898cd77b5e3 0x410015898cd77b5e 0x7013f9f9ffffffff 0xa7013f9f9fffffff

def z436 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0x01ecc04fc3380cf3 0x101ecc04fc3380cf

def z437 : W := mkw 0x3f7a07643e94ea2d 0x03f7a07643e94ea2 0xcfec06063c18c030 0x5cfec06063c18c03

def z438 : W := mkw 0x9fdea7670c14a021 0x09fdea7670c14a02 0xcfec06063c18c030 0x5cfec06063c18c03

def z439 : W := mkw 0x2970026032804a0c 0x02970026032804a0 0xd1f0067023c0cf0d 0x7d1f0067023c0cf0

def z440 : W := mkw 0x00215898e36b5dda 0xc00215898e36b5dd 0x7013f9f9e3ffffff 0xa7013f9f9e3fffff

def z441 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xee0f07863c1ff030 0xcee0f07863c1ff03

def z442 : W := mkw 0x0d1a200000000000 0x00d1a20000000000 0x0e13380000000000 0x80e1338000000000

def z443 : W := mkw 0x0000480001620000 0x0000048000162000 0x3013f9f003e73f0f 0xa3013f9f003e73f0

def z444 : W := mkw 0xc48ff89f897e0000 0x0c48ff89f897e000 0x000ff80fc03f0002 0x0000ff80fc03f000

def z445 : W := mkw 0x2b705f70f7e2ef4c 0x42b705f70f7e2ef4 0xfff0fff1ffc0ff0d 0xffff0fff1ffc0ff0

def z446 : W := mkw 0x100048004d77b5e3 0x4100048004d77b5e 0x700000003ffffff8 0x0700000003ffffff

def z447 : W := mkw 0x8fdfa7ef00000000 0x08fdfa7ef0000000 0x8fef078e00000006 0xf8fef078e0000000

def z448 : W := mkw 0x00e4da53e36a4d58 0xc00e4da53e36a4d5 0xd1fcfe7fe3f8cfff 0x7d1fcfe7fe3f8cff

def z449 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6fec00003fff0008 0x56fec00003fff000

def z450 : W := mkw 0x0001109880000000 0x0000110988000000 0x0003f809c0000002 0x00003f809c000000

def z451 : W := mkw 0x824117ffc00115c2 0x4824117ffc00115c 0x900007ffc0003fc4 0x0900007ffc0003fc

def z452 : W := mkw 0x89f4f273e3284c58 0x889f4f273e3284c5 0xd1fcfe7fe338ccff 0x7d1fcfe7fe338ccf

def z453 : W := mkw 0x5fbeed043ffea021 0x05fbeed043ffea02 0xeffffe063fffc03b 0xfeffffe063fffc03

def z454 : W := mkw 0x00005810c1620540 0x400005810c162054 0x3010f9f1c3c03f0d 0xa3010f9f1c3c03f0

def z455 : W := mkw 0x502048003fffb0a3 0x0502048003fffb0a 0x700000003ffff0f8 0x0700000003ffff0f

def z456 : W := mkw 0x2b70076032804a0c 0x02b70076032804a0 0x8ff007f003c00f05 0xf8ff007f003c00f0

def z457 : W := mkw 0x4ffeef603bfe0000 0x04ffeef603bfe000 0xeffffff03fff000f 0xfeffffff03fff000

def z458 : W := mkw 0x4dbff898bbff1182 0x44dbff898bbff118 0x6ffff9b03fff330b 0xf6ffff9b03fff330

def z459 : W := mkw 0x0000101080000000 0x0000010108000000 0x0010f871c0000001 0x00010f871c000000

def z460 : W := mkw 0x020005000400a000 0x0020005000400a00 0xfe1007f03fc0ff0d 0xefe1007f03fc0ff0

def z461 : W := mkw 0xcfdfbfff98d60000 0x0cfdfbfff98d6000 0xafffffffdcc70007 0xfafffffffdcc7000

def z462 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xc1ecc60fe038c0f2 0x5c1ecc60fe038c0f

def z463 : W := mkw 0x020005000400a000 0x0020005000400a00 0x2e0001801c003000 0x82e0001801c00300

def z464 : W := mkw 0x162b458c6f3dfcfb 0x8162b458c6f3dfcf 0xfe0f078e3f3ffcfe 0xefe0f078e3f3ffcf

def z465 : W := mkw 0xcdbff89fbbfe0000 0x0cdbff89fbbfe000 0x6ffff80fffff000b 0xf6ffff80fffff000

def z466 : W := mkw 0x140a000408140021 0x0140a00040814002 0x000c000600180030 0x0000c00060018003

def z467 : W := mkw 0x0bd4876300000000 0x00bd487630000000 0x8ffcc7ffc0000007 0xf8ffcc7ffc000000

def z468 : W := mkw 0x324107ec0401faaf 0x0324107ec0401faa 0x900007fe0000fff4 0x0900007fe0000fff

def z469 : W := mkw 0x5dbee8003fffb0a3 0x05dbee8003fffb0a 0x7ffff8003ffff0fb 0xf7ffff8003ffff0f

def z470 : W := mkw 0x2b70476077a0ee4c 0x02b70476077a0ee4 0xfff0c7f9ffe0ffcf 0xffff0c7f9ffe0ffc

def z471 : W := mkw 0x0060024022004808 0x0006002402200480 0xf1f007f023c0ff0d 0xff1f007f023c0ff0

def z472 : W := mkw 0x004112dbc0015dda 0xc004112dbc0015dd 0x900007ffc000fff4 0x0900007ffc000fff

def z473 : W := mkw 0x00005810c1620540 0x400005810c162054 0x2013f871c3e70f0b 0xa2013f871c3e70f0

def z474 : W := mkw 0x2b115db8d5e3b7c6 0x42b115db8d5e3b7c 0x3e13f9f9dfe73fcf 0xa3e13f9f9dfe73fc

def z475 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0x7e0301803c3ff0f8 0x87e0301803c3ff0f

def z476 : W := mkw 0x4dbee0003bbc0000 0x04dbee0003bbc000 0x4fecc0003f38000b 0x74fecc0003f38000

def z477 : W := mkw 0x00004800416315c2 0x400004800416315c 0x3000c049c3e73fcf 0x23000c049c3e73fc

def z478 : W := mkw 0x160b058c081510a3 0x0160b058c081510a 0x8e0f078e003f00f6 0xe8e0f078e003f00f

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00006002000c00c 0x6d00006002000c00

def z480 : W := mkw 0x0b10052000000000 0x00b1005200000000 0x0e1001b000000000 0x80e1001b00000000

def z481 : W := mkw 0x69f4ea6033ea4a0c 0x069f4ea6033ea4a0 0x01f0f87003c00f01 0x101f0f87003c00f0

def z482 : W := mkw 0x8fdff7ffc1200440 0x08fdff7ffc120044 0x9fffffffc3200ccf 0xf9fffffffc3200cc

def z483 : W := mkw 0x0000480001620000 0x0000048000162000 0x0010f80003c00001 0x00010f80003c0000

def z484 : W := mkw 0x562b4d8c3fffb0a3 0x0562b4d8c3fffb0a 0xfe0f078e3ffff0fe 0xefe0f078e3ffff0f

def z485 : W := mkw 0x8fdfb7ffc00115c2 0x48fdfb7ffc00115c 0x9fffffffc0003fc7 0xf9fffffffc0003fc

def z486 : W := mkw 0x4dfeea437bfe4c58 0x84dfeea437bfe4c5 0x6ffff841ffff0c0b 0xf6ffff841ffff0c0

def z487 : W := mkw 0x16efdfdfef7ffdfb 0xc16efdfdfef7ffdf 0xffffffffffffffff 0xffffffffffffffff

def z488 : W := mkw 0x9fdfffffcd77b5e3 0x49fdfffffcd77b5e 0xffffffffffffffff 0xffffffffffffffff

def z489 : W := mkw 0x040a000008140000 0x0040a00000814000 0x4e0c00003c180000 0x44e0c00003c18000

def z490 : W := mkw 0x8f1b35bc80000000 0x08f1b35bc8000000 0x8e1f3fbe00000006 0xe8e1f3fbe0000000

def z491 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x01fff80003ff0003 0x101fff80003ff000

def z492 : W := mkw 0x060b058c08140000 0x0060b058c0814000 0xee0f078e3c3f000e 0xeee0f078e3c3f000

def z493 : W := mkw 0x00a4c00063280440 0x000a4c0006328044 0x51ecc049e3380ccf 0x751ecc049e3380cc

def z494 : W := mkw 0x120005000c15b0a3 0x0120005000c15b0a 0xfe0007803c3ff0fc 0xefe0007803c3ff0f

def z495 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xc1ecc647e318cc31 0x5c1ecc647e318cc3

def z496 : W := mkw 0x0d9fb09880000000 0x00d9fb0988000000 0x0ffff9f9c0000007 0xf0ffff9f9c000000

def z497 : W := mkw 0x0000400041280450 0x8000040004128045 0x00000000003800f0 0x000000000003800f

def z498 : W := mkw 0x0000000040000440 0x0000000004000044 0x10000049c0000cc4 0x010000049c0000cc

def z499 : W := mkw 0x0000000000000000 0x0000000000000000 0x0013f80000000003 0xa0013f8000000000

def z500 : W := mkw 0x00e5dadbe36b5dda 0xc00e5dadbe36b5dd 0xd1effe4fe33fccff 0x7d1effe4fe33fccf

def z501 : W := mkw 0x1201058c0401b0a3 0x01201058c0401b0a 0x0000018000003000 0x0000001800000300

def z502 : W := mkw 0x9f1b35bc8c15b0a3 0x09f1b35bc8c15b0a 0x2e1339b01c073000 0x82e1339b01c07300

def z503 : W := mkw 0x6ffea7603e9cea0c 0x06ffea7603e9cea0 0xcfec06003c18c000 0x5cfec06003c18c00

def z504 : W := mkw 0x0b515ff8c16315c2 0x40b515ff8c16315c 0xbff3fff9c3e73fcf 0xfbff3fff9c3e73fc

def z505 : W := mkw 0x0d9ff898c16315c2 0x40d9ff898c16315c 0x3ffff9f9c3e73fcf 0xf3ffff9f9c3e73fc

def z506 : W := mkw 0x5fbffd9cffffb5e3 0x45fbffd9cffffb5e 0xffffffffffffffff 0xffffffffffffffff

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010007003c00f01 0x00010007003c00f0

def z508 : W := mkw 0xefffffffbffeea0c 0x0efffffffbffeea0 0xffffffffffffff0f 0xfffffffffffffff0

def z509 : W := mkw 0x140b008c081510a3 0x0140b008c081510a 0x6e0f000e3c3f00fa 0xe6e0f000e3c3f00f

def z510 : W := mkw 0x3fffc7ef7fbdfeff 0x83fffc7ef7fbdfef 0xffffc7ffffffffff 0xfffffc7fffffffff

def z511 : W := mkw 0x0f9fa58c00000000 0x00f9fa58c0000000 0x8fffff8e00000007 0xf8fffff8e0000000

def z512 : W := mkw 0x0020000022000000 0x0002000002200000 0x41e0000023000009 0x741e000002300000

def z513 : W := mkw 0x0020000022004808 0x0002000002200480 0x500000002300cc08 0x0500000002300cc0

def z514 : W := mkw 0xcf1b3dbc98d60000 0x0cf1b3dbc98d6000 0x2e1339b01cc70000 0x82e1339b01cc7000

def z515 : W := mkw 0x2b1005201480a204 0x02b1005201480a20 0x3e1001f01fc03f0d 0xa3e1001f01fc03f0

def z516 : W := mkw 0x1201159cc401b5e3 0x41201159cc401b5e 0x900007ffc000fff4 0x0900007ffc000fff

def z517 : W := mkw 0x49b4e8003bfe0000 0x049b4e8003bfe000 0x61f0f8003fff0009 0x161f0f8003fff000

def z518 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x2013f809c3e700cb 0xa2013f809c3e700c

def z519 : W := mkw 0xafffb7ffb2804a0c 0x0afffb7ffb2804a0 0x8fffffffc3c00f07 0xf8fffffffc3c00f0

def z520 : W := mkw 0x548fe88c097f10a3 0x0548fe88c097f10a 0x000ff80e003f00f2 0x0000ff80e003f00f

def z521 : W := mkw 0x2b5007600400ea0c 0x02b5007600400ea0 0x9ff007f00000ff05 0xf9ff007f00000ff0

def z522 : W := mkw 0x2bf487633688ea1c 0x82bf487633688ea1 0xcfec06063c18c030 0x5cfec06063c18c03

def z523 : W := mkw 0x060b5d9cc16315c2 0x4060b5d9cc16315c 0xbe1fffffc3e73fcf 0xebe1fffffc3e73fc

def z524 : W := mkw 0x8f9fb5bf80000000 0x08f9fb5bf8000000 0x0e1ff9bfc0000002 0x80e1ff9bfc000000

def z525 : W := mkw 0x0fdea76000000000 0x00fdea7600000000 0x8ffffff000000007 0xf8ffffff00000000

def z526 : W := mkw 0x2910002010800204 0x0291000201080020 0x0010003000c00300 0x00010003000c0030

def z527 : W := mkw 0x020005000400a000 0x0020005000400a00 0x900007800000f004 0x0900007800000f00

def z528 : W := mkw 0x442a48003bfe0000 0x0442a48003bfe000 0x6e0f00003fff000a 0xe6e0f00003fff000

def z529 : W := mkw 0xa9f4b273b2804a0c 0x0a9f4b273b2804a0 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z530 : W := mkw 0x2b1005201480a204 0x02b1005201480a20 0x0e0000001c000000 0x00e0000001c00000

def z531 : W := mkw 0xcffeef673bfe0000 0x0cffeef673bfe000 0xeffffe063fff000b 0xfeffffe063fff000

def z532 : W := mkw 0x0930000032800000 0x0093000003280000 0x4fe000003c000000 0x54fe000003c00000

def z533 : W := mkw 0x00e5dadbe36b5dda 0xc00e5dadbe36b5dd 0x31f3f9f9c3e73fcf 0xb31f3f9f9c3e73fc

def z534 : W := mkw 0x224007600400ea0c 0x0224007600400ea0 0xfe0007f03c00ff0c 0xefe0007f03c00ff0

def z535 : W := mkw 0x0001189880431182 0x4000118988043118 0x2013f9f9c0c73307 0xa2013f9f9c0c7330

def z536 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xffe007803c00f00c 0xfffe007803c00f00

def z537 : W := mkw 0x22e4c7636728ee5c 0x822e4c7636728ee5 0xd1ecc7ffe338ffff 0x7d1ecc7ffe338fff

def z538 : W := mkw 0x00204800636b5dda 0xc00204800636b5dd 0x7000000023fffff8 0x07000000023fffff

def z539 : W := mkw 0x00e5d2dbe3284c58 0x800e5d2dbe3284c5 0xd1ffffffe338ccff 0xfd1ffffffe338ccf

def z540 : W := mkw 0x0001189880431182 0x4000118988043118 0x301339f003c73f0d 0xa301339f003c73f0

def z541 : W := mkw 0x00015098c12115c2 0x400015098c12115c 0x1000c1f9c3203fcf 0x21000c1f9c3203fc

def z542 : W := mkw 0x362b058c3e95faaf 0x0362b058c3e95faa 0xfe0f078e3ffffffe 0xefe0f078e3ffffff

def z543 : W := mkw 0x160b159ccc15b5e3 0x4160b159ccc15b5e 0xfe0f07fffc3ffffe 0xefe0f07fffc3ffff

def z544 : W := mkw 0x302000003e95faaf 0x0302000003e95faa 0x700000003ffffff8 0x0700000003ffffff

def z545 : W := mkw 0x040b008c00000000 0x0040b008c0000000 0x000f000e00000002 0x0000f000e0000000

def z546 : W := mkw 0x848ff09fc1280450 0x8848ff09fc128045 0x000ff80fc03800f2 0x0000ff80fc03800f

def z547 : W := mkw 0x1201058c0401b0a3 0x01201058c0401b0a 0xb003078e0027f0fe 0xab003078e0027f0f

def z548 : W := mkw 0x8ddfb2ff80000000 0x08ddfb2ff8000000 0x01fff87fc0000003 0x101fff87fc000000

def z549 : W := mkw 0x8fffb7ffb2800000 0x08fffb7ffb280000 0xefffffffffc0000f 0xfefffffffffc0000

def z550 : W := mkw 0x160b058c0c14a021 0x0160b058c0c14a02 0xce0f078e3c18c036 0xece0f078e3c18c03

def z551 : W := mkw 0x0040024300000000 0x0004002430000000 0x8000064fc0000004 0x08000064fc000000

def z552 : W := mkw 0x09f4c24373a84c58 0x809f4c24373a84c5 0xfffcc64ffff8ccff 0xffffcc64ffff8ccf

def z553 : W := mkw 0x160b4d8c4d77b5e3 0x4160b4d8c4d77b5e 0xfe0f078e3ffffffe 0xefe0f078e3ffffff

def z554 : W := mkw 0x0b3005003680a000 0x00b3005003680a00 0xfff007803fc0f00d 0xffff007803fc0f00

def z555 : W := mkw 0x1f3b058c3e95b0a3 0x01f3b058c3e95b0a 0xffff078e3ffff0ff 0xfffff078e3ffff0f

def z556 : W := mkw 0x8fdea76700000000 0x08fdea7670000000 0x8fecc64fc0000007 0x78fecc64fc000000

def z557 : W := mkw 0x0040424341204c58 0x80040424341204c5 0x9000c64fc320ccff 0x29000c64fc320ccf

def z558 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0x91e0c64fc300ccf5 0x191e0c64fc300ccf

def z559 : W := mkw 0x06efc7cf63284c58 0x806efc7cf63284c5 0xdfefc7cfe338ccff 0xfdfefc7cfe338ccf

def z560 : W := mkw 0x5fffefcf7ffffcfb 0x85fffefcf7ffffcf 0xffffffcffffffcff 0xfffffffcffffffcf

def z561 : W := mkw 0x82c597ff80000000 0x082c597ff8000000 0x81ecc7ffc0000007 0x781ecc7ffc000000

def z562 : W := mkw 0x0950026000000000 0x0095002600000000 0x01f0007000000001 0x101f000700000000

def z563 : W := mkw 0x4d9ee800097e0000 0x04d9ee800097e000 0x0ffff800003f0003 0xf0ffff800003f000

def z564 : W := mkw 0x2ffea7603680ea0c 0x02ffea7603680ea0 0xfffffff03fc0ff0f 0xffffffff03fc0ff0

def z565 : W := mkw 0x0000400041200440 0x0000040004120044 0x0000c041c3000c01 0x00000c041c3000c0

def z566 : W := mkw 0x4d1b389898d71182 0x44d1b389898d7118 0x2e1339b01cc73300 0x82e1339b01cc7330

def z567 : W := mkw 0xcffffffffbff15c2 0x4cffffffffbff15c 0xffffffffffff3fcf 0xfffffffffffff3fc

def z568 : W := mkw 0x020105880401b082 0x0020105880401b08 0xfe0307883c27f0ce 0xefe0307883c27f0c

def z569 : W := mkw 0x2b5007601480ea0c 0x02b5007601480ea0 0xbe1007f01cc0ff04 0x8be1007f01cc0ff0

def z570 : W := mkw 0x20e4c24377a8ee5c 0x820e4c24377a8ee5 0xf1ecc64ffff8ffff 0x7f1ecc64ffff8fff

def z571 : W := mkw 0x848ea00700000000 0x0848ea0070000000 0x000c000600000000 0x0000c00060000000

def z572 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xcff007f03c00c005 0xfcff007f03c00c00

def z573 : W := mkw 0x00a4c00023280000 0x000a4c0002328000 0x01e0c00003000001 0x101e0c0000300000

def z574 : W := mkw 0x140b008c081510a3 0x0140b008c081510a 0xd00f060e203fc0fe 0x6d00f060e203fc0f

def z575 : W := mkw 0x4000080018d60000 0x04000080018d6000 0x200000001cc70000 0x0200000001cc7000

def z576 : W := mkw 0x5f1b2d8c1cd7b0a3 0x05f1b2d8c1cd7b0a 0x2e1339801cc73000 0x82e1339801cc7300

def z577 : W := mkw 0x000000000400a000 0x0000000000400a00 0x700000003c00f008 0x0700000003c00f00

def z578 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x300001f9c3e73fcc 0x0300001f9c3e73fc

def z579 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1ec06062338ccf8 0x5d1ec06062338ccf

def z580 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0307803c07f00c 0xefe0307803c07f00

def z581 : W := mkw 0x2bf487633680ea0c 0x02bf487633680ea0 0xfffcc7ffffc0ff0f 0xffffcc7ffffc0ff0

def z582 : W := mkw 0x8fdea76700000000 0x08fdea7670000000 0x8ffffe0600000003 0xf8ffffe060000000

def z583 : W := mkw 0xaf1b35bc9480a204 0x0af1b35bc9480a20 0x2e1339b01cc03300 0x82e1339b01cc0330

def z584 : W := mkw 0x16ef87cf2e1df8bb 0x816ef87cf2e1df8b 0xffef078e3c3ff0fe 0xfffef078e3c3ff0f

def z585 : W := mkw 0x448ea000081c0000 0x0448ea000081c000 0x000c000000180000 0x0000c00000018000

def z586 : W := mkw 0xcfffb7ffba9c0000 0x0cfffb7ffba9c000 0xcffffffffc180007 0xfcffffffffc18000

def z587 : W := mkw 0x8fdff7ffc1280450 0x88fdff7ffc128045 0x8fffffffc03800f7 0xf8fffffffc03800f

def z588 : W := mkw 0x8f9fb5bc80000000 0x08f9fb5bc8000000 0x0ffff9b000000003 0xf0ffff9b00000000

def z589 : W := mkw 0x948fb09f881510a3 0x0948fb09f881510a 0x000ff80fc03f00f2 0x0000ff80fc03f00f

def z590 : W := mkw 0x6dbee8003ffeea0c 0x06dbee8003ffeea0 0x7ffff8003fffff0b 0xf7ffff8003fffff0

def z591 : W := mkw 0x0060424063284c58 0x80060424063284c5 0xd1e006402338ccfd 0x7d1e006402338ccf

def z592 : W := mkw 0x3f7b07ec3e95faaf 0x03f7b07ec3e95faa 0xfff307f03fc7ff0d 0xffff307f03fc7ff0

def z593 : W := mkw 0x3b7007603e95faaf 0x03b7007603e95faa 0xfff007f03ffffffd 0xffff007f03ffffff

def z594 : W := mkw 0x00004800416315c2 0x400004800416315c 0x00000000002700c0 0x000000000002700c

def z595 : W := mkw 0x402048003bfe0000 0x0402048003bfe000 0x6013f8003fff000b 0xa6013f8003fff000

def z596 : W := mkw 0x29f4c26373a84e5c 0x829f4c26373a84e5 0x01f0c071c3c00f01 0x101f0c071c3c00f0

def z597 : W := mkw 0x00a4800022080000 0x000a480002208000 0x41ec000020180000 0x541ec00002018000

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000003c03f08 0x03000000003c03f0

def z599 : W := mkw 0x0001109880000000 0x0000110988000000 0x001339b000000000 0x8001339b00000000

def z600 : W := mkw 0x00000000400115c2 0x400000000400115c 0x1000000000003fc0 0x01000000000003fc

def z601 : W := mkw 0x5fbfa58c3e9db0a3 0x05fbfa58c3e9db0a 0xffef078e3c3ff0fe 0xfffef078e3c3ff0f

def z602 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c000e003800f2 0x0000c000e003800f

def z603 : W := mkw 0x49b4e80033ea0000 0x049b4e80033ea000 0x21f3f80003e7000b 0xb21f3f80003e7000

def z604 : W := mkw 0x0001008800011082 0x0000100880001108 0x10000188000030c4 0x010000188000030c

def z605 : W := mkw 0x140b589cc97715e3 0x4140b589cc97715e 0x301ff9ffc3ff3fff 0xa301ff9ffc3ff3ff

def z606 : W := mkw 0x00a4c00063284c58 0x800a4c00063284c5 0x51ecc0002338ccfb 0x751ecc0002338ccf

def z607 : W := mkw 0x4dbea0003a9c0000 0x04dbea0003a9c000 0x6fef00003c3f000a 0xf6fef00003c3f000

def z608 : W := mkw 0x2b7117f8f681ffce 0x42b7117f8f681ffc 0xfff007f9ffc0ffcd 0xffff007f9ffc0ffc

def z609 : W := mkw 0x00a5d898e36b15c2 0x400a5d898e36b15c 0x71fff9f9e3ff3fcf 0xf71fff9f9e3ff3fc

def z610 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xdfe006403f00cc0d 0x7dfe006403f00cc0

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0x200300000027000a 0xa200300000027000

def z612 : W := mkw 0xaffffffff7e3ffce 0x4affffffff7e3ffc 0xffffffffffe7ffcf 0xfffffffffffe7ffc

def z613 : W := mkw 0x8fffb7ffa2004808 0x08fffb7ffa200480 0xdfffffffe300cc0f 0xfdfffffffe300cc0

def z614 : W := mkw 0x824117ffc0004c58 0x8824117ffc0004c5 0x900007ffc000ccf4 0x0900007ffc000ccf

def z615 : W := mkw 0x364b07ec0c15faaf 0x0364b07ec0c15faa 0xfe0f07fe3c3ffffe 0xefe0f07fe3c3ffff

def z616 : W := mkw 0x0b70076032800000 0x00b7007603280000 0xeff007f03fc0000d 0xfeff007f03fc0000

def z617 : W := mkw 0x4dfeea433bfe4818 0x84dfeea433bfe481 0xeffffe063fffc03b 0xfeffffe063fffc03

def z618 : W := mkw 0x060a05000c14a000 0x0060a05000c14a00 0xfe0f07803c3ff00e 0xefe0f07803c3ff00

def z619 : W := mkw 0x0b50076000000000 0x00b5007600000000 0xbff007f003c03f0d 0xfbff007f003c03f0

def z620 : W := mkw 0x49b4e80033ea0000 0x049b4e80033ea000 0x41fcf80023f8000b 0x741fcf80023f8000

def z621 : W := mkw 0x89f4f273e3284c58 0x889f4f273e3284c5 0x01f0f871c3000c01 0x101f0f871c3000c0

def z622 : W := mkw 0xaf7b37fcb680ea0c 0x0af7b37fcb680ea0 0xfff33ff03fc0ff0d 0xffff33ff03fc0ff0

def z623 : W := mkw 0x49b4e80033ea0000 0x049b4e80033ea000 0x6ff0f8003fc00009 0xf6ff0f8003fc0000

def z624 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0x41ecc041e3380c0b 0x741ecc041e3380c0

def z625 : W := mkw 0x00e4c24023284808 0x000e4c2402328480 0xd1ecc6402338cc0f 0x7d1ecc6402338cc0

def z626 : W := mkw 0x00e4824322084818 0x800e482432208481 0x01e0000000000000 0x101e000000000000

def z627 : W := mkw 0x5dbfe88c3bff10a3 0x05dbfe88c3bff10a 0x6ffff80e3fff00fb 0xf6ffff80e3fff00f

def z628 : W := mkw 0xafffb7ffb680ea0c 0x0afffb7ffb680ea0 0xcffffffffc00c007 0xfcffffffffc00c00

def z629 : W := mkw 0x8f1b3dbc80431182 0x48f1b3dbc8043118 0x2e1339b000c73300 0x82e1339b000c7330

def z630 : W := mkw 0x168fc58f4d3db4f3 0x8168fc58f4d3db4f 0xfe0fc78ffc3ff0fe 0xefe0fc78ffc3ff0f

def z631 : W := mkw 0x04eec2436b3c4c58 0x804eec2436b3c4c5 0xffefc64fff3fccff 0xfffefc64fff3fccf

def z632 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x1010f9f9c3c03fc5 0x01010f9f9c3c03fc

def z633 : W := mkw 0x060b058c00000000 0x0060b058c0000000 0xde0f078e2038c0fe 0xede0f078e2038c0f

def z634 : W := mkw 0x0020400063284c58 0x80020400063284c5 0xd00c060e2338ccfe 0x6d00c060e2338ccf

def z635 : W := mkw 0x2970026032804a0c 0x02970026032804a0 0x31f001f003c03f0d 0xb31f001f003c03f0

def z636 : W := mkw 0x40215898fbff15c2 0x440215898fbff15c 0x7013f9f9ffff3fcf 0xa7013f9f9ffff3fc

def z637 : W := mkw 0x140a00000c15b0a3 0x0140a00000c15b0a 0x7e0f00003c3ff0fa 0xe7e0f00003c3ff0f

def z638 : W := mkw 0x0085d89bc16b15d2 0xc0085d89bc16b15d 0x000ff80fc03f00f2 0x0000ff80fc03f00f

def z639 : W := mkw 0x00a4c800236a0000 0x000a4c800236a000 0x61fff80023ff000b 0xf61fff80023ff000

def z640 : W := mkw 0x8fdfbfff80431182 0x48fdfbfff8043118 0xafffffffc0c73307 0xfafffffffc0c7330

def z641 : W := mkw 0x40a4c8003bfe0000 0x040a4c8003bfe000 0x61ecc0003fff000b 0x761ecc0003fff000

def z642 : W := mkw 0x8001109f80000000 0x08001109f8000000 0x0000000fc0000000 0x00000000fc000000

def z643 : W := mkw 0x0001589881620000 0x0000158988162000 0x2013f9f9c3e7000f 0xa2013f9f9c3e7000

def z644 : W := mkw 0x49b5f898f3eb15c2 0x449b5f898f3eb15c 0x31f3f9f9c3e73fcf 0xb31f3f9f9c3e73fc

def z645 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x0013f9f9c02700c7 0xa0013f9f9c02700c

def z646 : W := mkw 0x00c4c24341284c58 0x800c4c24341284c5 0x900cc64fc038ccf6 0x0900cc64fc038ccf

def z647 : W := mkw 0x00c4c24341280450 0x800c4c2434128045 0x81ecc64fc03800f7 0x781ecc64fc03800f

def z648 : W := mkw 0x448ee803497e0450 0x8448ee803497e045 0x000ff80fc03f00f2 0x0000ff80fc03f00f

def z649 : W := mkw 0x0001109880000000 0x0000110988000000 0x3013f9f9c3c03f0f 0xa3013f9f9c3c03f0

def z650 : W := mkw 0x0d9ee80001620000 0x00d9ee8000162000 0x2ffff80003e7000b 0xf2ffff80003e7000

def z651 : W := mkw 0x00011098c00115c2 0x400011098c00115c 0x1013f9f9c0003fc7 0xa1013f9f9c0003fc

def z652 : W := mkw 0x2b704f6077e3ffce 0x42b704f6077e3ffc 0xfff007f03fe7ffcd 0xffff007f03fe7ffc

def z653 : W := mkw 0x160b5d9ccd77b5e3 0x4160b5d9ccd77b5e 0x3e13f9f9dfe73fcf 0xa3e13f9f9dfe73fc

def z654 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xdfe007f03c00ff04 0x5dfe007f03c00ff0

def z655 : W := mkw 0x4dbea0003a9c0000 0x04dbea0003a9c000 0x4ffff8003c180003 0xf4ffff8003c18000

def z656 : W := mkw 0x0084c00001280000 0x00084c0000128000 0x000cc00000380002 0x0000cc0000038000

def z657 : W := mkw 0x4dfffadbfbff5dda 0xc4dfffadbfbff5dd 0xffffffffffffffff 0xffffffffffffffff

def z658 : W := mkw 0x120005040400a021 0x0120005040400a02 0x800006060000c030 0x0800006060000c03

def z659 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x4ffcf8003fd80001 0x54ffcf8003fd8000

def z660 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xae0f078e1c073006 0xeae0f078e1c07300

def z661 : W := mkw 0x14efc2cf6b3d5cfb 0x814efc2cf6b3d5cf 0xd1efc64fe33fccff 0x7d1efc64fe33fccf

def z662 : W := mkw 0x0040024300004818 0x8004002430000481 0x800006060000c030 0x0800006060000c03

def z663 : W := mkw 0x4dbff898fbff15c2 0x44dbff898fbff15c 0x6ffff809ffff00cb 0xf6ffff809ffff00c

def z664 : W := mkw 0x2bf4c76037a8ea0c 0x02bf4c76037a8ea0 0xfffcc7f03ff8ff0f 0xffffcc7f03ff8ff0

def z665 : W := mkw 0x0b70076022004808 0x00b7007602200480 0xdff007f02300cc0d 0xfdff007f02300cc0

def z666 : W := mkw 0xcfdfffff897e0000 0x0cfdfffff897e000 0x8fffffffc03f0007 0xf8fffffffc03f000

def z667 : W := mkw 0x0001189880431182 0x4000118988043118 0x301339b800e733ce 0xa301339b800e733c

def z668 : W := mkw 0x3f1b05ac1c95b2a7 0x03f1b05ac1c95b2a 0xfe1f07be3cfff3fe 0xefe1f07be3cfff3f

def z669 : W := mkw 0x6fbeed203ffea204 0x06fbeed203ffea20 0x6ffff9b03fff330b 0xf6ffff9b03fff330

def z670 : W := mkw 0x09315898f3e315c2 0x409315898f3e315c 0x7ff3f9f9ffe73fcf 0xf7ff3f9f9ffe73fc

def z671 : W := mkw 0x2b111db894c3b386 0x42b111db894c3b38 0x2e1339b01cc73300 0x82e1339b01cc7330

def z672 : W := mkw 0x1201058c0c15b0a3 0x01201058c0c15b0a 0xf000078e3c3ff0fc 0x0f000078e3c3ff0f

def z673 : W := mkw 0x8f1b35bc80000000 0x08f1b35bc8000000 0x0e13f9f9c0000007 0xa0e13f9f9c000000

def z674 : W := mkw 0x00415adbc1635dda 0xc00415adbc1635dd 0xb013ffffc3e7ffff 0xab013ffffc3e7fff

def z675 : W := mkw 0x4d9ee80019fe0000 0x04d9ee80019fe000 0x2e1ff8001cff0002 0x82e1ff8001cff000

def z676 : W := mkw 0x4084e800016a0000 0x04084e800016a000 0x0000f80000000000 0x00000f8000000000

def z677 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0x11e0c049c3200ccf 0x311e0c049c3200cc

def z678 : W := mkw 0xabf4b773b680ea0c 0x0abf4b773b680ea0 0xfff0fff1ffc0ff0d 0xffff0fff1ffc0ff0

def z679 : W := mkw 0x4dbea0003a9c0000 0x04dbea0003a9c000 0x6ffc00003fd80009 0xf6ffc00003fd8000

def z680 : W := mkw 0x848ff89fc16315c2 0x4848ff89fc16315c 0x000ff80fc02700c2 0x0000ff80fc02700c

def z681 : W := mkw 0x09b4c00033a80000 0x009b4c00033a8000 0x6ffcc0003ff8000b 0xf6ffcc0003ff8000

def z682 : W := mkw 0x4dfeea433bfe0000 0x04dfeea433bfe000 0xeffffe4fffff000f 0xfeffffe4fffff000

def z683 : W := mkw 0x4dbff898bbfe0000 0x04dbff898bbfe000 0x6ffff9f9ffff000f 0xf6ffff9f9ffff000

def z684 : W := mkw 0x0000400041200440 0x0000040004120044 0x0000c009c02000c2 0x00000c009c02000c

def z685 : W := mkw 0x8fffffffe36b5dda 0xc8fffffffe36b5dd 0xffffffffe3ffffff 0xfffffffffe3fffff

def z686 : W := mkw 0x0000080000420000 0x0000008000042000 0x2013380000c70000 0x82013380000c7000

def z687 : W := mkw 0x00e4ca43636b5dda 0xc00e4ca43636b5dd 0xf1ecc64fe3ffffff 0x7f1ecc64fe3fffff

def z688 : W := mkw 0x2f7b07ec3680ea0c 0x02f7b07ec3680ea0 0xffff07fe3fc0ff0f 0xfffff07fe3fc0ff0

def z689 : W := mkw 0x0000400041200440 0x0000040004120044 0x1000000003200cc8 0x01000000003200cc

def z690 : W := mkw 0x20215898f7e3ffce 0x420215898f7e3ffc 0x7013f9f9ffe7ffcf 0xa7013f9f9ffe7ffc

def z691 : W := mkw 0x0060024022004808 0x0006002402200480 0xc1e006002000c000 0x5c1e006002000c00

def z692 : W := mkw 0x2020400077a8ee5c 0x82020400077a8ee5 0x700000003ff8fff8 0x0700000003ff8fff

def z693 : W := mkw 0x5fbea5043e9ca021 0x05fbea5043e9ca02 0xcfec06063c18c030 0x5cfec06063c18c03

def z694 : W := mkw 0x4d1a680019f60000 0x04d1a680019f6000 0x2e13f8001fe7000b 0xa2e13f8001fe7000

def z695 : W := mkw 0x2bf4c76377a8ee5c 0x82bf4c76377a8ee5 0xdfecc64fff38ccff 0x7dfecc64fff38ccf

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x500000002038c0f8 0x0500000002038c0f

def z697 : W := mkw 0x16ee87472e1ce839 0x816ee87472e1ce83 0xcfec06063c18c030 0x5cfec06063c18c03

def z698 : W := mkw 0x200000000400ea0c 0x0200000000400ea0 0x100000000000ff00 0x0100000000000ff0

def z699 : W := mkw 0x8fffb7ffa2084818 0x88fffb7ffa208481 0xcfffffffe018c037 0xfcfffffffe018c03

def z700 : W := mkw 0x4910280010c20000 0x04910280010c2000 0x0010380000c00000 0x00010380000c0000

def z701 : W := mkw 0x0000480001620000 0x0000048000162000 0x0003f80000270002 0x00003f8000027000

def z702 : W := mkw 0x2f7a07603e94ea0c 0x02f7a07603e94ea0 0xffff07f03fffff0f 0xfffff07f03fffff0

def z703 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xbe03078e1c07f0f4 0x8be03078e1c07f0f

def z704 : W := mkw 0x100000000401b0a3 0x0100000000401b0a 0x100000000000f0f0 0x0100000000000f0f

def z705 : W := mkw 0x84eff2dfe3284c58 0x884eff2dfe3284c5 0xd1effe4fe338ccff 0x7d1effe4fe338ccf

def z706 : W := mkw 0x164b07cf4c15fcfb 0x8164b07cf4c15fcf 0xfe0f07cffc3ffcfe 0xefe0f07cffc3ffcf

def z707 : W := mkw 0x09d4a24300000000 0x009d4a2430000000 0x81fcfe4fc0000007 0x781fcfe4fc000000

def z708 : W := mkw 0x00c4c24341284c58 0x800c4c24341284c5 0x91ecc64fc038ccf7 0x791ecc64fc038ccf

def z709 : W := mkw 0x16efc7cf6f3dfcfb 0x816efc7cf6f3dfcf 0x2fe3c1c1df073c01 0x92fe3c1c1df073c0

def z710 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfffc07f63fd8ff3d 0xffffc07f63fd8ff3

def z711 : W := mkw 0x8fdfb7ff80011082 0x08fdfb7ff8001108 0x9fffffffc00030c7 0xf9fffffffc00030c

def z712 : W := mkw 0x2b715ff8f7e3ffce 0x42b715ff8f7e3ffc 0xcfe3fe09fc27c0c2 0x5cfe3fe09fc27c0c

def z713 : W := mkw 0x00c4824300000000 0x000c482430000000 0x81fffe4fc0000007 0xf81fffe4fc000000

def z714 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8ff3ffffc0000005 0x98ff3ffffc000000

def z715 : W := mkw 0x160a05040c15b0a3 0x0160a05040c15b0a 0xfe0c060e3c3ff0fe 0x6fe0c060e3c3ff0f

def z716 : W := mkw 0x4dbea0003a9c0000 0x04dbea0003a9c000 0x6ffff8003c3f000b 0xf6ffff8003c3f000

def z717 : W := mkw 0x8ddeb27780000000 0x08ddeb2778000000 0x01fcf877c0000001 0x101fcf877c000000

def z718 : W := mkw 0x00c592db80000000 0x000c592db8000000 0x81effe4fc0000007 0x781effe4fc000000

def z719 : W := mkw 0x4dbea8003ade0000 0x04dbea8003ade000 0x6ffff8003cdf0003 0xf6ffff8003cdf000

def z720 : W := mkw 0x00214888636b5dda 0xc00214888636b5dd 0xf00f078e23fffffe 0xef00f078e23fffff

def z721 : W := mkw 0x2b3005203680a204 0x02b3005203680a20 0x7ff001f03fc03f0d 0xf7ff001f03fc03f0

def z722 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xf1efc64fe33fccff 0xff1efc64fe33fccf

def z723 : W := mkw 0x8fdfb7ff8400a000 0x08fdfb7ff8400a00 0xafffffffdc003007 0xfafffffffdc00300

def z724 : W := mkw 0x8f3b75bce3284c58 0x88f3b75bce3284c5 0x5e1339b02338ccf8 0x85e1339b02338ccf

def z725 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xffffffffffffffff 0xffffffffffffffff

def z726 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8fffffffc03800f7 0xf8fffffffc03800f

def z727 : W := mkw 0x4020480073ea4c58 0x84020480073ea4c5 0x0000000003c00c00 0x00000000003c00c0

def z728 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ffff8003fdf0001 0xd6ffff8003fdf000

def z729 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0f060e3c3ff0fa 0x4fe0f060e3c3ff0f

def z730 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x2013f9f9c3c73f07 0xa2013f9f9c3c73f0

def z731 : W := mkw 0xbf1b35bc9c95b2a7 0x0bf1b35bc9c95b2a 0x2e1339b01cc73300 0x82e1339b01cc7330

def z732 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xce0f078e3c3fc0f6 0xece0f078e3c3fc0f

def z733 : W := mkw 0x2b94c52355a8a654 0x82b94c52355a8a65 0x2e1cc1bfdcf833f2 0x82e1cc1bfdcf833f

def z734 : W := mkw 0x3d7b02ec3a955aaf 0x03d7b02ec3a955aa 0x01ff007e03ff0ff3 0x101ff007e03ff0ff

def z735 : W := mkw 0x00e4ca43636a4c58 0x800e4ca43636a4c5 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z736 : W := mkw 0x0d3a48003bf60000 0x00d3a48003bf6000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z737 : W := mkw 0xafdfb7ff90800204 0x0afdfb7ff9080020 0x8fffffffc0c00307 0xf8fffffffc0c0030

def z738 : W := mkw 0xdf1b3dbc9cd7b0a3 0x0df1b3dbc9cd7b0a 0x2e1339b01cc73000 0x82e1339b01cc7300

def z739 : W := mkw 0x00c4925380000000 0x000c492538000000 0x01f0f871c0000001 0x101f0f871c000000

def z740 : W := mkw 0x324117fcc401ffef 0x4324117fcc401ffe 0x900007ffc000fff4 0x0900007ffc000fff

def z741 : W := mkw 0x8ddeb27380000000 0x08ddeb2738000000 0x0ff3f871c0000001 0x90ff3f871c000000

def z742 : W := mkw 0x3b7007643680ea2d 0x03b7007643680ea2 0xfff007f63fc0ff3d 0xffff007f63fc0ff3

def z743 : W := mkw 0x602048007fffffce 0x4602048007fffffc 0x700000003fffffc8 0x0700000003fffffc

def z744 : W := mkw 0x20e4c24373a84e5c 0x820e4c24373a84e5 0xd1ecc64fe3f8cfff 0x7d1ecc64fe3f8cff

def z745 : W := mkw 0xa9d4b27390800204 0x0a9d4b2739080020 0x01f0f871c0c00301 0x101f0f871c0c0030

def z746 : W := mkw 0x0970024032804808 0x0097002403280480 0xfff007f03fc0ff0d 0xffff007f03fc0ff0

def z747 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfff007b03fc0ff08 0xdfff007b03fc0ff0

def z748 : W := mkw 0x9fdfb7ff881510a3 0x09fdfb7ff881510a 0xdfffffffe03fc0ff 0xfdfffffffe03fc0f

def z749 : W := mkw 0x84cfb2df80000000 0x084cfb2df8000000 0x81ffffffc0000007 0xf81ffffffc000000

def z750 : W := mkw 0x402048007bfe0540 0x4402048007bfe054 0x600000003fff0f08 0x0600000003fff0f0

def z751 : W := mkw 0x160b159c8c15b0a3 0x0160b159c8c15b0a 0xfe1f3fbe3c3ff0fe 0xefe1f3fbe3c3ff0f

def z752 : W := mkw 0x8fdfb7ff88140000 0x08fdfb7ff8814000 0xcffffffffc180007 0xfcffffffffc18000

def z753 : W := mkw 0xc48ff89fc97f15c2 0x4c48ff89fc97f15c 0x000ff80fc03f00c2 0x0000ff80fc03f00c

def z754 : W := mkw 0x00c4c24341200440 0x000c4c2434120044 0xd1ecc64fe338ccff 0x7d1ecc64fe338ccf

def z755 : W := mkw 0x4d9ee800097e0000 0x04d9ee800097e000 0x6ffff8003c3f000b 0xf6ffff8003c3f000

def z756 : W := mkw 0xc2615fffbbfe0000 0x0c2615fffbbfe000 0xe00007ffffff000c 0x0e00007ffffff000

def z757 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xee0f060e3c3fc0fa 0xeee0f060e3c3fc0f

def z758 : W := mkw 0x9fdfb7ff8c14a021 0x09fdfb7ff8c14a02 0xeffffffffc3fc03f 0xfeffffffffc3fc03

def z759 : W := mkw 0x89d5b2fb80000000 0x089d5b2fb8000000 0x81ffffffc0000007 0xf81ffffffc000000

def z760 : W := mkw 0x4dbea8003ade0000 0x04dbea8003ade000 0x6fff38003fdf0009 0xf6fff38003fdf000

def z761 : W := mkw 0x8fdeb77780000000 0x08fdeb7778000000 0x8fecfe07c0000000 0x58fecfe07c000000

def z762 : W := mkw 0x00e4824322004808 0x000e482432200480 0xd1ecc64fe338ccff 0x7d1ecc64fe338ccf

def z763 : W := mkw 0x924117ffc401b5e3 0x4924117ffc401b5e 0x900007ffc000fff4 0x0900007ffc000fff

def z764 : W := mkw 0x89d5b2fb80011082 0x089d5b2fb8001108 0x31f3f9f9c02730cf 0xb31f3f9f9c02730c

def z765 : W := mkw 0x4dbfb098fa9d15c2 0x44dbfb098fa9d15c 0x5fec01f9fc183fc4 0x55fec01f9fc183fc

def z766 : W := mkw 0x86cfb7df80000000 0x086cfb7df8000000 0x8fefffcfc0000007 0xf8fefffcfc000000

def z767 : W := mkw 0x160b159c8c15b0a3 0x0160b159c8c15b0a 0xfe1fffffffffffff 0xefe1ffffffffffff

def z768 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xee0f078e3c3ff0f2 0xcee0f078e3c3ff0f

def z769 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0xeffffe0e3fff000f 0xfeffffe0e3fff000

def z770 : W := mkw 0x8bd5b7ff80000000 0x08bd5b7ff8000000 0x01f0f9f1c0000001 0x101f0f9f1c000000

def z771 : W := mkw 0x00e4ca43636a4c58 0x800e4ca43636a4c5 0xd1effe4fe33fccff 0x7d1effe4fe33fccf

def z772 : W := mkw 0x848fb09f80000000 0x0848fb09f8000000 0x01eff80fc0000003 0x701eff80fc000000

def z773 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x4ffff8003fff0003 0x54ffff8003fff000

def z774 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8ffffff7c0000001 0xd8ffffff7c000000

def z775 : W := mkw 0x80c4b25380000000 0x080c4b2538000000 0x01e0f841c0000001 0x101e0f841c000000

def z776 : W := mkw 0x99d4b2738c15b0a3 0x099d4b2738c15b0a 0x71f0f871fc3ff0f9 0x171f0f871fc3ff0f

def z777 : W := mkw 0x124117dfc401fdfb 0xc124117dfc401fdf 0x900007ffc000fff4 0x0900007ffc000fff

def z778 : W := mkw 0x0f9fb59c80000000 0x00f9fb59c8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z779 : W := mkw 0x402048007bff15c2 0x4402048007bff15c 0x600000003fff00c8 0x0600000003fff00c

def z780 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x7ffff9803fff300f 0xf7ffff9803fff300

def z781 : W := mkw 0x4020480073ea0540 0x44020480073ea054 0x0000000003c00f00 0x00000000003c00f0

def z782 : W := mkw 0x4d5a2a4358d64c58 0x84d5a2a4358d64c5 0xbe133e4fdcc7ccf4 0x8be133e4fdcc7ccf

def z783 : W := mkw 0x160a5d14cd76a561 0x4160a5d14cd76a56 0xce1cfe77ffd8cf31 0x4ce1cfe77ffd8cf3

def z784 : W := mkw 0x160a05040c15b0a3 0x0160a05040c15b0a 0xce0c06063c3fc0f0 0x4ce0c06063c3fc0f

def z785 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xdff007f03fc0ff05 0x5dff007f03fc0ff0

def z786 : W := mkw 0x00a4c00063280440 0x000a4c0006328044 0xd1ecc64fe338ccff 0x7d1ecc64fe338ccf

def z787 : W := mkw 0x8ddfb2df80000000 0x08ddfb2df8000000 0x8ffffe4fc0000007 0xf8ffffe4fc000000

def z788 : W := mkw 0x0b70076032800000 0x00b7007603280000 0xfff007f03fc03f0d 0xffff007f03fc03f0

def z789 : W := mkw 0x00e4c24373a84c58 0x800e4c24373a84c5 0xf1ecc64ffff8ccff 0x7f1ecc64ffff8ccf

def z790 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x3013f9f1c3c73f0d 0xa3013f9f1c3c73f0

def z791 : W := mkw 0x0085909880000000 0x0008590988000000 0x01fff9f9c0000007 0xf01fff9f9c000000

def z792 : W := mkw 0xcdbee8073bfe0000 0x0cdbee8073bfe000 0x6ffff8063fff000b 0xf6ffff8063fff000

def z793 : W := mkw 0x442a48007bfe4c58 0x8442a48007bfe4c5 0xfe0f060e3fffccfe 0xefe0f060e3fffccf

def z794 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ffff8703fff0f0b 0xf6ffff8703fff0f0

def z795 : W := mkw 0x924117ffc401fcfb 0x8924117ffc401fcf 0x900007ffc000fcf4 0x0900007ffc000fcf

def z796 : W := mkw 0x8fdfb7ff8400a000 0x08fdfb7ff8400a00 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z797 : W := mkw 0x00e59adba24b599a 0xc00e59adba24b599 0xe1ff3fb620dff330 0xde1ff3fb620dff33

def z798 : W := mkw 0x16cf97df8c15b0a3 0x016cf97df8c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z799 : W := mkw 0x4d9ea80018d60000 0x04d9ea80018d6000 0x6ffff8003cff000b 0xf6ffff8003cff000

def z800 : W := mkw 0x4d3a68003bfe0000 0x04d3a68003bfe000 0x6ff338003fff0009 0xf6ff338003fff000

def z801 : W := mkw 0x4dbee8007bfe0440 0x04dbee8007bfe044 0x7ffff8003fff0ccb 0xf7ffff8003fff0cc

def z802 : W := mkw 0x2020480077ebffde 0xc2020480077ebffd 0x700000003ffffff8 0x0700000003ffffff

def z803 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe1f07fe3c3ff0ff 0xefe1f07fe3c3ff0f

def z804 : W := mkw 0x86cfb7ff80000000 0x086cfb7ff8000000 0x81efffffc0000007 0x781efffffc000000

def z805 : W := mkw 0x00a4c00363280450 0x800a4c0036328045 0xd1ecc60fe338c0ff 0x7d1ecc60fe338c0f

def z806 : W := mkw 0x66ceef600d7eea0c 0x066ceef600d7eea0 0x900ffff0003fff06 0x0900ffff0003fff0

def z807 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x81f0fe71c0000005 0x781f0fe71c000000

def z808 : W := mkw 0x8fdfb7ff88140000 0x08fdfb7ff8814000 0xafffffffdc070007 0xfafffffffdc07000

def z809 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x1013f9f9c3e73fc7 0x01013f9f9c3e73fc

def z810 : W := mkw 0x224117f88401fb8e 0x4224117f88401fb8 0x900007f00000ff04 0x0900007f00000ff0

def z811 : W := mkw 0x4dbee8007bfe0540 0x44dbee8007bfe054 0x6ffff8003fff0f0b 0xf6ffff8003fff0f0

def z812 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8ffffe0fc0000003 0xf8ffffe0fc000000

def z813 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xdfffffffe000c00f 0xfdfffffffe000c00

def z814 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x301ff9ffc3ff3fff 0xa301ff9ffc3ff3ff

def z815 : W := mkw 0x8fdfb7ff88140000 0x08fdfb7ff8814000 0xfffffffffc3fc0ff 0xffffffffffc3fc0f

def z816 : W := mkw 0x8ddfb2ff80000000 0x08ddfb2ff8000000 0x81fffe7fc0000007 0x781fffe7fc000000

def z817 : W := mkw 0x0000480041620440 0x0000048004162044 0x3013f9f9c3e73fcf 0xa3013f9f9c3e73fc

def z818 : W := mkw 0x5bb5ed8c37ebb0a3 0x05bb5ed8c37ebb0a 0x91f0ff8e03c0f0f5 0x191f0ff8e03c0f0f

def z819 : W := mkw 0x160b159c8c15b0a3 0x0160b159c8c15b0a 0xfe0fff8ffc3ff0fe 0xefe0fff8ffc3ff0f

def z820 : W := mkw 0x94cfb2df881510a3 0x094cfb2df881510a 0xd1effe4fe03fc0ff 0x7d1effe4fe03fc0f

def z821 : W := mkw 0x9fdfb7ff8400a021 0x09fdfb7ff8400a02 0x8fffffffc000c037 0xf8fffffffc000c03

def z822 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x01fcf87fc0000003 0x101fcf87fc000000

def z823 : W := mkw 0x0d9ea00300000000 0x00d9ea0030000000 0x0ffff80fc0000003 0xf0ffff80fc000000

def z824 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xf1ecc7cfe338fcff 0xff1ecc7cfe338fcf

def z825 : W := mkw 0x562b4d8c7fffb5e3 0x4562b4d8c7fffb5e 0xfe0f078e3ffffffe 0xefe0f078e3ffffff

def z826 : W := mkw 0x8fdfb7ff88140000 0x08fdfb7ff8814000 0x8fffffffc03f0007 0xf8fffffffc03f000

def z827 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0xb01fffffc3e73fcf 0xeb01fffffc3e73fc

def z828 : W := mkw 0x140a00000c15b0a3 0x0140a00000c15b0a 0xfe0f060e3c3ff0fe 0xefe0f060e3c3ff0f

def z829 : W := mkw 0x0b50177080000000 0x00b5017708000000 0x8ff0fff1c0000005 0xf8ff0fff1c000000

def z830 : W := mkw 0x502048007fffb5e3 0x4502048007fffb5e 0x700000003ffffff8 0x0700000003ffffff

def z831 : W := mkw 0x360b05ac0c15b2a7 0x0360b05ac0c15b2a 0xfe0f07be3c3ff3fe 0xefe0f07be3c3ff3f

def z832 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xffecc64fff38ccff 0xfffecc64fff38ccf

def z833 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfff007f83fe0ffcf 0xffff007f83fe0ffc

def z834 : W := mkw 0x1f5b17fc8c15b0a3 0x01f5b17fc8c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z835 : W := mkw 0x4dbea8003ade0000 0x04dbea8003ade000 0x4fef38003c1f0000 0x54fef38003c1f000

def z836 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0x91ecc64fc338ccf7 0x191ecc64fc338ccf

def z837 : W := mkw 0xbffea7673e94ea2d 0x0bffea7673e94ea2 0xcfec06063c18c030 0x5cfec06063c18c03

def z838 : W := mkw 0x4dbee8007bfe4c58 0x84dbee8007bfe4c5 0x6ffff8003fff0c0b 0xf6ffff8003fff0c0

def z839 : W := mkw 0x8fdeb77780000000 0x08fdeb7778000000 0x8ffcfff7c0000005 0xf8ffcfff7c000000

def z840 : W := mkw 0x0b5117f88401b082 0x00b5117f88401b08 0xfff3fff9fc27f0cf 0xffff3fff9fc27f0c

def z841 : W := mkw 0x0d9fb09888151082 0x00d9fb0988815108 0x7ffff9f9fc3f30cf 0xf7ffff9f9fc3f30c

def z842 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x2013f9f1c3e73f0b 0xa2013f9f1c3e73f0

def z843 : W := mkw 0xa4afb09fb680ea0c 0x0a4afb09fb680ea0 0x700ff80fffc0ff0a 0x0700ff80fffc0ff0

def z844 : W := mkw 0x00e4824362084c58 0x800e4824362084c5 0xd1ec064fe318ccfd 0x7d1ec064fe318ccf

def z845 : W := mkw 0x8fdfb7ff80011082 0x08fdfb7ff8001108 0xafffffffc0073007 0xfafffffffc007300

def z846 : W := mkw 0x0d9eb01080000000 0x00d9eb0108000000 0x0ffff871c0000003 0xf0ffff871c000000

def z847 : W := mkw 0x960b359c8c15b0a3 0x0960b359c8c15b0a 0xfe0f3f8e3c3ff0fe 0xefe0f3f8e3c3ff0f

def z848 : W := mkw 0xbfdfb7ff9c95b2a7 0x0bfdfb7ff9c95b2a 0xfffffffffcfff3ff 0xffffffffffcfff3f

def z849 : W := mkw 0x2b7007633680ea0c 0x02b7007633680ea0 0xfff007ffffc0ff0d 0xffff007ffffc0ff0

def z850 : W := mkw 0x302048007ff7ffef 0x4302048007ff7ffe 0x700000003ffffff8 0x0700000003ffffff

def z851 : W := mkw 0x8fdeef67416315c2 0x48fdeef67416315c 0xbfec060603e73fc8 0x5bfec060603e73fc

def z852 : W := mkw 0x69f4ea6373ea4e5c 0x869f4ea6373ea4e5 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z853 : W := mkw 0x9bd5b7ff8401b0a3 0x09bd5b7ff8401b0a 0x91f0ffffc000f0f5 0x191f0ffffc000f0f

def z854 : W := mkw 0x0fdfa7cf00000000 0x00fdfa7cf0000000 0x8fffffcfc0000007 0xf8fffffcfc000000

def z855 : W := mkw 0x4dbee8007bfe0440 0x04dbee8007bfe044 0x7ffff9f9ffff3fcf 0xf7ffff9f9ffff3fc

def z856 : W := mkw 0x49f4fa53f3ea4d58 0xc49f4fa53f3ea4d5 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z857 : W := mkw 0x402048007bfe0450 0x8402048007bfe045 0x600000003fff00f8 0x0600000003fff00f

def z858 : W := mkw 0x1fdfa7cf0c15b0a3 0x01fdfa7cf0c15b0a 0xffffffcffc3ff0ff 0xfffffffcffc3ff0f

def z859 : W := mkw 0x4d1a280018d60000 0x04d1a280018d6000 0x2ff338001cc70001 0xf2ff338001cc7000

def z860 : W := mkw 0x8fdeb77780000000 0x08fdeb7778000000 0x8ffcfe7fc0000007 0x78ffcfe7fc000000

def z861 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x7ffff8003fff3f0b 0xf7ffff8003fff3f0

def z862 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x0ff0f871c0000001 0xf0ff0f871c000000

def z863 : W := mkw 0x9fdfb7ff8401b0a3 0x09fdfb7ff8401b0a 0xbfffffffc027f0ff 0xfbfffffffc027f0f

def z864 : W := mkw 0x89d5b2ff80000000 0x089d5b2ff8000000 0x01f0f87fc0000001 0x101f0f87fc000000

def z865 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x7ffff8083fff00cf 0xf7ffff8083fff00c

def z866 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0f07ce3f3ffcff 0xefe0f07ce3f3ffcf

def z867 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0fc7cffc3ff0ff 0xefe0fc7cffc3ff0f

def z868 : W := mkw 0x9f1b3dbc8c57b1a3 0x49f1b3dbc8c57b1a 0x2e1339b01cc73300 0x82e1339b01cc7330

def z869 : W := mkw 0x4dbee8007bfe4c58 0x84dbee8007bfe4c5 0x7ffff849ffffccff 0xf7ffff849ffffccf

def z870 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0x7ff001f03fc0ff09 0x97ff001f03fc0ff0

def z871 : W := mkw 0x0001589881620000 0x0000158988162000 0x3013f9f9c3e73f0f 0xa3013f9f9c3e73f0

def z872 : W := mkw 0x2b5007601480a204 0x02b5007601480a20 0xbff007f01fc03f0d 0xfbff007f01fc03f0

def z873 : W := mkw 0x9fdfb7ff88140021 0x09fdfb7ff8814002 0x8fffffffc0180037 0xf8fffffffc018003

def z874 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x4ffff8003c3f0003 0xf4ffff8003c3f000

def z875 : W := mkw 0x362b4d8c7ff7ffef 0x4362b4d8c7ff7ffe 0xfe0f078e3ffffffe 0xefe0f078e3ffffff

def z876 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ffff9b03fff330b 0xf6ffff9b03fff330

def z877 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0xfffffe003fffc00f 0xffffffe003fffc00

def z878 : W := mkw 0x96cfb7df8c15b0a3 0x096cfb7df8c15b0a 0xffefffcffc3ff0ff 0xfffefffcffc3ff0f

def z879 : W := mkw 0x8ddfb2ff80000000 0x08ddfb2ff8000000 0x0ffff87fc0000003 0xf0ffff87fc000000

def z880 : W := mkw 0x0020480073e315c2 0x40020480073e315c 0x700000003fe73fc8 0x0700000003fe73fc

def z881 : W := mkw 0x5f1b3d9c9cd7b1a3 0x45f1b3d9c9cd7b1a 0x2e1339b01cc73300 0x82e1339b01cc7330

def z882 : W := mkw 0x960b15bc8c15b0a3 0x0960b15bc8c15b0a 0xfe0f07be3c3ff0fe 0xefe0f07be3c3ff0f

def z883 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x2013f9f9c3e73fc3 0x82013f9f9c3e73fc

def z884 : W := mkw 0xeffea7673e9cea0c 0x0effea7673e9cea0 0xcfec06063c18c000 0x5cfec06063c18c00

def z885 : W := mkw 0x402048006b7e4c58 0x8402048006b7e4c5 0x50000000233fccf8 0x050000000233fccf

def z886 : W := mkw 0xcfdfb7ff98940000 0x0cfdfb7ff9894000 0x8fffffffdc000007 0xf8fffffffdc00000

def z887 : W := mkw 0x00204800636a4d58 0xc00204800636a4d5 0x0000000003c00f00 0x00000000003c00f0

def z888 : W := mkw 0x4dbee8003bfe4818 0x84dbee8003bfe481 0x6ffff8003fffc03b 0xf6ffff8003fffc03

def z889 : W := mkw 0x0dbee0002b3c0000 0x00dbee0002b3c000 0x6ffff8003f3f000b 0xf6ffff8003f3f000

def z890 : W := mkw 0x8fdfb7ff80004808 0x08fdfb7ff8000480 0x9fffffffc000cc07 0xf9fffffffc000cc0

def z891 : W := mkw 0x402048007bfe0440 0x0402048007bfe044 0x700000003fff0cc8 0x0700000003fff0cc

def z892 : W := mkw 0x2020480073e35fce 0x42020480073e35fc 0x3000000003e73fc8 0x03000000003e73fc

def z893 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x4feff8003f3f000b 0x74feff8003f3f000

def z894 : W := mkw 0x0d9fb09880000000 0x00d9fb0988000000 0x0ffff809c0000003 0xf0ffff809c000000

def z895 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xfffffffffc07f00f 0xffffffffffc07f00

def z896 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x0ff3f9f9c0000007 0xb0ff3f9f9c000000

def z897 : W := mkw 0x4dbee8037bfe0450 0x84dbee8037bfe045 0x7ffff84fffff0cff 0xf7ffff84fffff0cf

def z898 : W := mkw 0x00e4824362084c58 0x800e4824362084c5 0xd1ecc64fe018ccf7 0x7d1ecc64fe018ccf

def z899 : W := mkw 0x160a05040c15b0a3 0x0160a05040c15b0a 0xfe0f06063c3ff0fa 0xefe0f06063c3ff0f

def z900 : W := mkw 0x4dbee8003bfe4808 0x04dbee8003bfe480 0x7ffff8003fffcc0b 0xf7ffff8003fffcc0

def z901 : W := mkw 0x00015898c16b15d2 0xc00015898c16b15d 0x3013f9f9c3ff3fff 0xa3013f9f9c3ff3ff

def z902 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0f07fe3c3ffffe 0xefe0f07fe3c3ffff

def z903 : W := mkw 0x4d3a28003ad60000 0x04d3a28003ad6000 0x6ff338003cc70000 0xd6ff338003cc7000

def z904 : W := mkw 0x1001589cc16315e3 0x41001589cc16315e 0x3013f9ffc3e73fff 0xa3013f9ffc3e73ff

def z905 : W := mkw 0x8fdfb7ff8400a000 0x08fdfb7ff8400a00 0xfffffffffc38f0ff 0xffffffffffc38f0f

def z906 : W := mkw 0xb24117ff8401faaf 0x0b24117ff8401faa 0x900007ffc000fff4 0x0900007ffc000fff

def z907 : W := mkw 0x4dbee8033bfe0010 0x84dbee8033bfe001 0x6ffff8063fff003b 0xf6ffff8063fff003

def z908 : W := mkw 0x9fdfb7ff881510a3 0x09fdfb7ff881510a 0xbfffffffc03f30ff 0xfbfffffffc03f30f

def z909 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0x3ff001f01fc03f0d 0xb3ff001f01fc03f0

def z910 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfff3fff03fc0ff0f 0xffff3fff03fc0ff0

def z911 : W := mkw 0xafdfb7ff9480a204 0x0afdfb7ff9480a20 0xfffffffffcc0f30f 0xffffffffffcc0f30

def z912 : W := mkw 0x060b058c08140000 0x0060b058c0814000 0xfe0f078e3c3fc0fe 0xefe0f078e3c3fc0f

def z913 : W := mkw 0x4dbea8003ad60000 0x04dbea8003ad6000 0x6ffff8003fc7000b 0xf6ffff8003fc7000

def z914 : W := mkw 0x8ddfb2ff80000000 0x08ddfb2ff8000000 0x01eff80fc0000002 0x101eff80fc000000

def z915 : W := mkw 0x0dbea0003a940000 0x00dbea0003a94000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z916 : W := mkw 0x0f5b17fc80000000 0x00f5b17fc8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z917 : W := mkw 0x8bd4b77380000000 0x08bd4b7738000000 0x8ff0fe71c0000001 0x58ff0fe71c000000

def z918 : W := mkw 0x924117ff8401b0a3 0x0924117ff8401b0a 0x800007ffc0003004 0x0800007ffc000300

def z919 : W := mkw 0x0001109880011082 0x0000110988001108 0x3013f9f9c3e73fcf 0xa3013f9f9c3e73fc

def z920 : W := mkw 0x6dbee8003bfe4a0c 0x06dbee8003bfe4a0 0x6ffff8003fff0f0b 0xf6ffff8003fff0f0

def z921 : W := mkw 0x8f5b37fc80000000 0x08f5b37fc8000000 0x8ff3fff9c0000007 0xf8ff3fff9c000000

def z922 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x9fffffffc0003f07 0xf9fffffffc0003f0

def z923 : W := mkw 0x004112d880000000 0x0004112d88000000 0x81f3fff9c0000007 0xf81f3fff9c000000

def z924 : W := mkw 0x0ddea24300000000 0x00ddea2430000000 0x0ffff841c0000003 0xf0ffff841c000000

def z925 : W := mkw 0x4d3a28003ad60000 0x04d3a28003ad6000 0x2ff338001fc70001 0x92ff338001fc7000

def z926 : W := mkw 0x442b48887bff15c2 0x4442b48887bff15c 0x7e0f01883fff3fce 0xe7e0f01883fff3fc

def z927 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfff007f03ff8fffd 0xffff007f03ff8fff

def z928 : W := mkw 0x2b7007633680ea1c 0x82b7007633680ea1 0xfff007f63fc0ff3d 0xffff007f63fc0ff3

def z929 : W := mkw 0x8bd4b77780000000 0x08bd4b7778000000 0x81f0fe77c0000001 0x181f0fe77c000000

def z930 : W := mkw 0x00c4c24341280450 0x800c4c2434128045 0xd1ecc64fe038c0ff 0x7d1ecc64fe038c0f

def z931 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8ffffe7fc0000003 0x58ffffe7fc000000

def z932 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xdffffffffc18f0f7 0xfdffffffffc18f0f

def z933 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x3013f9f1c3e73fc9 0x83013f9f1c3e73fc

def z934 : W := mkw 0x4dbee8007bfe0450 0x84dbee8007bfe045 0x6ffff8003fff00fb 0xf6ffff8003fff00f

def z935 : W := mkw 0x8fdfb7ff80080010 0x88fdfb7ff8008001 0x8fffffffc0180037 0xf8fffffffc018003

def z936 : W := mkw 0x2020480077e2ef4c 0x42020480077e2ef4 0x700000003fc0ff08 0x0700000003fc0ff0

def z937 : W := mkw 0x8fdeb77780000000 0x08fdeb7778000000 0x8ffffe77c0000003 0xf8ffffe77c000000

def z938 : W := mkw 0x20211098b680ea0c 0x020211098b680ea0 0x7013f9f9ffc0ff0f 0xa7013f9f9ffc0ff0

def z939 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x0ffff9f1c0000003 0xf0ffff9f1c000000

def z940 : W := mkw 0x82c597ff80000000 0x082c597ff8000000 0x81ffffffc0000007 0xf81ffffffc000000

def z941 : W := mkw 0x8bd4b77380000000 0x08bd4b7738000000 0x8ffcffffc0000007 0xf8ffcffffc000000

def z942 : W := mkw 0x04cea24300000000 0x004cea2430000000 0x81effe4fc0000007 0x781effe4fc000000

def z943 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ffff849ffff000f 0xf6ffff849ffff000

def z944 : W := mkw 0x06cf97df80000000 0x006cf97df8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z945 : W := mkw 0x4d3a68003bf60000 0x04d3a68003bf6000 0x6ff3f8003fe7000b 0xf6ff3f8003fe7000

def z946 : W := mkw 0x293000003680ea0c 0x0293000003680ea0 0x7ff001f03fc0ff0d 0xf7ff001f03fc0ff0

def z947 : W := mkw 0x9fdfb7ff881510a3 0x09fdfb7ff881510a 0xeffffffffc3f00ff 0xfeffffffffc3f00f

def z948 : W := mkw 0x00204800636a4c58 0x800204800636a4c5 0x7000000023ffccf8 0x07000000023ffccf

def z949 : W := mkw 0x0911109880000000 0x0091110988000000 0x0ff3f9f9c0000007 0xf0ff3f9f9c000000

def z950 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe1f078e3ffff0ff 0xefe1f078e3ffff0f

def z951 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xc1ecc64fe338ccf3 0x5c1ecc64fe338ccf

def z952 : W := mkw 0x4dbea8003ade0000 0x04dbea8003ade000 0x2ff338001cc70000 0x92ff338001cc7000

def z953 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xeff007f03fc0ff01 0xdeff007f03fc0ff0

def z954 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xffe007f03fc0ff0c 0x5ffe007f03fc0ff0

def z955 : W := mkw 0x40e4ea43636a4c58 0x840e4ea43636a4c5 0xd1ecfe4fe338ccff 0x7d1ecfe4fe338ccf

def z956 : W := mkw 0x5dbee8043bfe0021 0x05dbee8043bfe002 0x6ffff8063fff003b 0xf6ffff8063fff003

def z957 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x3013f9f9c3c73fc5 0x83013f9f9c3c73fc

def z958 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xbfffffffc000300f 0xfbfffffffc000300

def z959 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfff007fe3fc0fffd 0xffff007fe3fc0fff

def z960 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x81f0fe7fc0000005 0x181f0fe7fc000000

def z961 : W := mkw 0x148fd89fc97f15f3 0xc148fd89fc97f15f 0x000ff80fc03f00f2 0x0000ff80fc03f00f

def z962 : W := mkw 0x8fdfb7ff80011082 0x08fdfb7ff8001108 0x8fffffffc02700c7 0xf8fffffffc02700c

def z963 : W := mkw 0x89d5b2fb80000000 0x089d5b2fb8000000 0x01f0f9f9c0000005 0x101f0f9f9c000000

def z964 : W := mkw 0x8fdfb7ff90800000 0x08fdfb7ff9080000 0xafffffffdcc00007 0xfafffffffdcc0000

def z965 : W := mkw 0x4dbee8007bfe0440 0x04dbee8007bfe044 0xfffffe4fffffccff 0xffffffe4fffffccf

def z966 : W := mkw 0x00e4ca43636a4d58 0xc00e4ca43636a4d5 0xd1ecc64fe3f8cfff 0x7d1ecc64fe3f8cff

def z967 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0xb013ffffc3e7ffff 0xab013ffffc3e7fff

def z968 : W := mkw 0xafdfb7ff9480ea0c 0x0afdfb7ff9480ea0 0xbfffffffdcc0ff07 0xfbfffffffdcc0ff0

def z969 : W := mkw 0x020105880401b082 0x0020105880401b08 0xfe0f078e3c3ff0fe 0xefe0f078e3c3ff0f

def z970 : W := mkw 0x160b159c8c15b1a3 0x4160b159c8c15b1a 0xfe0f07be3c3ff3fe 0xefe0f07be3c3ff3f

def z971 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xcfffffffe018c037 0xfcfffffffe018c03

def z972 : W := mkw 0x8ddeb27380000000 0x08ddeb2738000000 0x8ffffe7fc0000007 0xf8ffffe7fc000000

def z973 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xbfffffffdc07f0f7 0xfbfffffffdc07f0f

def z974 : W := mkw 0x8bd5b7ff80000000 0x08bd5b7ff8000000 0x8ff0ffffc0000005 0xf8ff0ffffc000000

def z975 : W := mkw 0x29f4da73f3ea4f5c 0xc29f4da73f3ea4f5 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z976 : W := mkw 0x162b4d8c6f7ffdfb 0xc162b4d8c6f7ffdf 0xfe0f078e3ffffffe 0xefe0f078e3ffffff

def z977 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe1f07be3cfff3fe 0xefe1f07be3cfff3f

def z978 : W := mkw 0x8ddfb2fb80000000 0x08ddfb2fb8000000 0x0ffff9f9c0000007 0xf0ffff9f9c000000

def z979 : W := mkw 0x00c592db80000000 0x000c592db8000000 0x01f3f9f9c0000007 0xb01f3f9f9c000000

def z980 : W := mkw 0x8bd4b7738400a000 0x08bd4b7738400a00 0xfff0fff1fc00f00d 0xffff0fff1fc00f00

def z981 : W := mkw 0xafdfb7ff80004a0c 0x0afdfb7ff80004a0 0x8fffffffc0000f07 0xf8fffffffc0000f0

def z982 : W := mkw 0x00204800636a4d58 0xc00204800636a4d5 0x5000000023f8cff8 0x05000000023f8cff

def z983 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x01e0f801c0000000 0x101e0f801c000000

def z984 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ffff80e3fff00fb 0xf6ffff80e3fff00f

def z985 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x9fffffffc3000c0f 0xf9fffffffc3000c0

def z986 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6fff38003fff0008 0xd6fff38003fff000

def z987 : W := mkw 0x8fdfb7ff80004818 0x88fdfb7ff8000481 0x8fffffffc000c037 0xf8fffffffc000c03

def z988 : W := mkw 0x00c4824340004c58 0x800c4824340004c5 0xd1ecc64fe038ccff 0x7d1ecc64fe038ccf

def z989 : W := mkw 0xa9d4b27380004a0c 0x0a9d4b27380004a0 0x01f0f871c0000f01 0x101f0f871c0000f0

def z990 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1ecc64fe318ccf5 0x5d1ecc64fe318ccf

def z991 : W := mkw 0x8ddfb2ff80000000 0x08ddfb2ff8000000 0x01fff9ffc0000007 0xb01fff9ffc000000

def z992 : W := mkw 0x602048007ffeee5c 0x8602048007ffeee5 0x700000003ffffff8 0x0700000003ffffff

def z993 : W := mkw 0x562b4d8c7ffffcfb 0x8562b4d8c7ffffcf 0xfe0f078e3ffffcfe 0xefe0f078e3ffffcf

def z994 : W := mkw 0x102048006f7ffdfb 0xc102048006f7ffdf 0x700000003ffffff8 0x0700000003ffffff

def z995 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xafffffffc0c03307 0xfafffffffc0c0330

def z996 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1ecc7ffe338ffff 0x7d1ecc7ffe338fff

def z997 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xaff007f01fc03f05 0xfaff007f01fc03f0

def z998 : W := mkw 0x502048007ffffcfb 0x8502048007ffffcf 0x700000003ffffcf8 0x0700000003ffffcf

def z999 : W := mkw 0x6ffea7633e9cea1c 0x86ffea7633e9cea1 0xcfec06063c18c030 0x5cfec06063c18c03

def z1000 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0x9fffffffc03ff0f7 0xf9fffffffc03ff0f

def z1001 : W := mkw 0xafdfb7ff9480a204 0x0afdfb7ff9480a20 0x8fffffffdc000007 0xf8fffffffdc00000

def z1002 : W := mkw 0x00c4925380000000 0x000c492538000000 0x81fcfe7fc0000007 0x781fcfe7fc000000

def z1003 : W := mkw 0x0bd597fb80000000 0x00bd597fb8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1004 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x701ff9f9e3ff3fcf 0xe701ff9f9e3ff3fc

def z1005 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x2ff3f8001fe7000b 0xb2ff3f8001fe7000

def z1006 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xf1fcc64fe3f8ccff 0xff1fcc64fe3f8ccf

def z1007 : W := mkw 0x0d9ea00008140000 0x00d9ea0000814000 0x2ffff8001c070003 0xf2ffff8001c07000

def z1008 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xeffffffffc00000f 0xfeffffffffc00000

def z1009 : W := mkw 0x8fdea76700000000 0x08fdea7670000000 0x8ffffe4fc0000007 0xf8ffffe4fc000000

def z1010 : W := mkw 0x80c4b25380000000 0x080c4b2538000000 0x81ecfe4fc0000007 0x781ecfe4fc000000

def z1011 : W := mkw 0x9fdfb7ff800110a3 0x09fdfb7ff800110a 0x8fffffffc00000f7 0xf8fffffffc00000f

def z1012 : W := mkw 0x0ddfb2db80000000 0x00ddfb2db8000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1013 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8fffffffc3c00f07 0xf8fffffffc3c00f0

def z1014 : W := mkw 0x22404f600562ea0c 0x022404f600562ea0 0xb013fff003e7ff0f 0xab013fff003e7ff0

def z1015 : W := mkw 0x8fdfb7ff80011082 0x08fdfb7ff8001108 0xffffffffe03ff0ff 0xfffffffffe03ff0f

def z1016 : W := mkw 0x448ff89bc97f15d2 0xc448ff89bc97f15d 0x000ff80fc03f00f2 0x0000ff80fc03f00f

def z1017 : W := mkw 0x9fdeb7778c14a021 0x09fdeb7778c14a02 0xcffcfe77fc18c031 0x5cffcfe77fc18c03

def z1018 : W := mkw 0x4020480073ea4c58 0x84020480073ea4c5 0x5000000023f8ccf8 0x05000000023f8ccf

def z1019 : W := mkw 0x8d9fb09f80000000 0x08d9fb09f8000000 0x01fff80fc0000003 0x101fff80fc000000

def z1020 : W := mkw 0x4dbee8007bfe0440 0x04dbee8007bfe044 0x6ffff841ffff0c0b 0xf6ffff841ffff0c0

def z1021 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x81fcfe77c0000001 0x581fcfe77c000000

def z1022 : W := mkw 0x0fdea76300000000 0x00fdea7630000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1023 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x01f0f871c3c00f01 0x101f0f871c3c00f0

def z1024 : W := mkw 0x0d9ea00000000000 0x00d9ea0000000000 0x0ffff849c0000007 0xf0ffff849c000000

def z1025 : W := mkw 0x22214d8877e3ffce 0x422214d8877e3ffc 0xfe0307883fe7ffce 0xefe0307883fe7ffc

def z1026 : W := mkw 0x0d9ee80009760000 0x00d9ee8000976000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z1027 : W := mkw 0x49b4e80033ea0000 0x049b4e80033ea000 0x6ff3f8003fe7000b 0xf6ff3f8003fe7000

def z1028 : W := mkw 0x20e4c26363284e5c 0x820e4c26363284e5 0xd1ecc67fe338cfff 0x7d1ecc67fe338cff

def z1029 : W := mkw 0x4d9ea80018d60000 0x04d9ea80018d6000 0x2ff3f8001cc70001 0x92ff3f8001cc7000

def z1030 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xbfffffffdc2730cf 0xfbfffffffdc2730c

def z1031 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xcfffffffe038000f 0xfcfffffffe038000

def z1032 : W := mkw 0x2b3005203680ea0c 0x02b3005203680ea0 0x7ff001b03fc0ff09 0xf7ff001b03fc0ff0

def z1033 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8fefff8fc0000006 0xf8fefff8fc000000

def z1034 : W := mkw 0x9fdfb7ff8401b0a3 0x09fdfb7ff8401b0a 0x8fffffffc0003007 0xf8fffffffc000300

def z1035 : W := mkw 0x0995b09880000000 0x00995b0988000000 0x01f3f9f9c0000007 0xb01f3f9f9c000000

def z1036 : W := mkw 0x09b4c80033ea0000 0x009b4c80033ea000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z1037 : W := mkw 0x9fdfb7ff8c14a021 0x09fdfb7ff8c14a02 0xfffffffffc18f03f 0xffffffffffc18f03

def z1038 : W := mkw 0x095112f880000000 0x0095112f88000000 0x01f3f9f9c0000007 0xb01f3f9f9c000000

def z1039 : W := mkw 0x8bd4b77380000000 0x08bd4b7738000000 0x81f0fff1c0000005 0x181f0fff1c000000

def z1040 : W := mkw 0x00e4824322084818 0x800e482432208481 0xd1ecc64fe038c0ff 0x7d1ecc64fe038c0f

def z1041 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1ec064fe338ccfc 0x5d1ec064fe338ccf

def z1042 : W := mkw 0x060a05000c14a000 0x0060a05000c14a00 0xfe0f078e3c3ff0fe 0xefe0f078e3c3ff0f

def z1043 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x9fffffffc000c0f7 0xf9fffffffc000c0f

def z1044 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x7e13f9f9ffe73fcf 0xe7e13f9f9ffe73fc

def z1045 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0f078e3ffffffe 0xefe0f078e3ffffff

def z1046 : W := mkw 0x4d9ea80018d60000 0x04d9ea80018d6000 0x2fff38001cc70000 0xd2fff38001cc7000

def z1047 : W := mkw 0x2020480073e24f4c 0x42020480073e24f4 0x0000000003c00f00 0x00000000003c00f0

def z1048 : W := mkw 0x4d9ee80019fe0000 0x04d9ee80019fe000 0x2ffff8001cff0003 0xf2ffff8001cff000

def z1049 : W := mkw 0x8fdeb77380000000 0x08fdeb7738000000 0x8ffffff1c0000007 0xf8ffffff1c000000

def z1050 : W := mkw 0x89d5b2fb80000000 0x089d5b2fb8000000 0x01f3f9f1c0000001 0x901f3f9f1c000000

def z1051 : W := mkw 0x00e4ca43636a4c58 0x800e4ca43636a4c5 0xd1fcfe4fe3f8ccff 0x7d1fcfe4fe3f8ccf

def z1052 : W := mkw 0x0dbee80033e20000 0x00dbee80033e2000 0x6ffff8003fe7000b 0xf6ffff8003fe7000

def z1053 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0x2ff3f9f1dc073001 0x92ff3f9f1dc07300

def z1054 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x81ffffffc0000007 0x181ffffffc000000

def z1055 : W := mkw 0x8fdfb7ff80011082 0x08fdfb7ff8001108 0xbfffffffc3e73fcf 0xfbfffffffc3e73fc

def z1056 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xeffffffffc1ff037 0xfeffffffffc1ff03

def z1057 : W := mkw 0x9d9fb09f881510a3 0x09d9fb09f881510a 0x6ffff80ffc3f00fb 0xf6ffff80ffc3f00f

def z1058 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0c078e3c3ff0fc 0x4fe0c078e3c3ff0f

def z1059 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0x6ff001f03fc03f09 0xf6ff001f03fc03f0

def z1060 : W := mkw 0x0ddea24308140000 0x00ddea2430814000 0xfffffe4ffc3fc0ff 0xffffffe4ffc3fc0f

def z1061 : W := mkw 0x160a05040c14a021 0x0160a05040c14a02 0xfe0f060e3c3fc0fe 0xefe0f060e3c3fc0f

def z1062 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1ecc60fe338ccfa 0x5d1ecc60fe338ccf

def z1063 : W := mkw 0x0fdfb7f880000000 0x00fdfb7f88000000 0x8ffffff9c0000007 0xf8ffffff9c000000

def z1064 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xafffffffc3c0000f 0xfafffffffc3c0000

def z1065 : W := mkw 0x00204800636b15c2 0x400204800636b15c 0x7000000023ff3fc8 0x07000000023ff3fc

def z1066 : W := mkw 0x8fdfb7ff8400a000 0x08fdfb7ff8400a00 0x9fffffffc000f007 0xf9fffffffc000f00

def z1067 : W := mkw 0x4dbee8037bfe0450 0x84dbee8037bfe045 0xfffffe0fffffc0ff 0xffffffe0fffffc0f

def z1068 : W := mkw 0x948ff89fc97715e3 0x4948ff89fc97715e 0x000ff80fc03f00f2 0x0000ff80fc03f00f

def z1069 : W := mkw 0xa24117ffc401ffce 0x4a24117ffc401ffc 0x900007ffc000ffc4 0x0900007ffc000ffc

def z1070 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe1fff8e3c3ff0ff 0xefe1fff8e3c3ff0f

def z1071 : W := mkw 0x040b008808151082 0x0040b00880815108 0xfe0f078e3c3ff0fe 0xefe0f078e3c3ff0f

def z1072 : W := mkw 0x402048007bfe4c58 0x8402048007bfe4c5 0x600000003fff0c08 0x0600000003fff0c0

def z1073 : W := mkw 0x8ddeb27380000000 0x08ddeb2738000000 0x01fff871c0000003 0x101fff871c000000

def z1074 : W := mkw 0x1f9fb59c8c15b0a3 0x01f9fb59c8c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z1075 : W := mkw 0x0020480063635dca 0x40020480063635dc 0x7000000023e7ffc8 0x07000000023e7ffc

def z1076 : W := mkw 0x0930080032c20000 0x00930080032c2000 0x6ff338003fc70009 0xf6ff338003fc7000

def z1077 : W := mkw 0x00e4824362084c58 0x800e4824362084c5 0xd1ec064fe038ccfe 0x7d1ec064fe038ccf

def z1078 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x01f0f9f1c0000005 0xb01f0f9f1c000000

def z1079 : W := mkw 0x0994b01080000000 0x00994b0108000000 0x01f0f871c0000001 0x101f0f871c000000

def z1080 : W := mkw 0x00204800636b5dda 0xc00204800636b5dd 0x3000000003e73fc8 0x03000000003e73fc

def z1081 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfff307f03fe7ff0f 0xffff307f03fe7ff0

def z1082 : W := mkw 0x2970026032804a0c 0x02970026032804a0 0x7ff001f03fc03f0d 0xf7ff001f03fc03f0

def z1083 : W := mkw 0x0060024362004c58 0x80060024362004c5 0xd1ec064fe338ccff 0x7d1ec064fe338ccf

def z1084 : W := mkw 0x4dbee8037bfe4c58 0x84dbee8037bfe4c5 0x7ffff80fffffccfb 0xf7ffff80fffffccf

def z1085 : W := mkw 0x0950127080000000 0x0095012708000000 0x01f0f871c0000001 0x101f0f871c000000

def z1086 : W := mkw 0xafdfb7ff9480a204 0x0afdfb7ff9480a20 0xbfffffffdfc03f0f 0xfbfffffffdfc03f0

def z1087 : W := mkw 0x160b159c8c15b0a3 0x0160b159c8c15b0a 0xfe0f07fffc3ff0fe 0xefe0f07fffc3ff0f

def z1088 : W := mkw 0x4d3a28003ad60000 0x04d3a28003ad6000 0x6fff38003fff000b 0xf6fff38003fff000

def z1089 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8ff3fff1c0000005 0xf8ff3fff1c000000

def z1090 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1ecc64fe038ccf6 0x5d1ecc64fe038ccf

def z1091 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ffff8003cff0002 0xd6ffff8003cff000

def z1092 : W := mkw 0xcfdfb7ff881c0000 0x0cfdfb7ff881c000 0x8fffffffc0180007 0xf8fffffffc018000

def z1093 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x7ffff8003fffc0fb 0xf7ffff8003fffc0f

def z1094 : W := mkw 0xbfdfb7ff8c15faaf 0x0bfdfb7ff8c15faa 0xfffffffffc3fffff 0xffffffffffc3ffff

def z1095 : W := mkw 0xab7007673680ea0c 0x0ab7007673680ea0 0xfff007f63fc0ff0d 0xffff007f63fc0ff0

def z1096 : W := mkw 0x00e4c24323280000 0x000e4c2432328000 0xd1ecc64fe338c0ff 0x7d1ecc64fe338c0f

def z1097 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x9fffffffc02000cf 0xf9fffffffc02000c

def z1098 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xde0f060e3c3fc0fe 0x6de0f060e3c3fc0f

def z1099 : W := mkw 0x8bd4b77380000000 0x08bd4b7738000000 0x0ff0f9f1c0000001 0x90ff0f9f1c000000

def z1100 : W := mkw 0x40e4ca4373ea4c58 0x840e4ca4373ea4c5 0xd1ecc64fe3f8ccff 0x7d1ecc64fe3f8ccf

def z1101 : W := mkw 0x2b7007603688ea1c 0x82b7007603688ea1 0xfff007f03fd8ff3d 0xffff007f03fd8ff3

def z1102 : W := mkw 0x0b5007600400a000 0x00b5007600400a00 0xfff007f03fc0ff0d 0xffff007f03fc0ff0

def z1103 : W := mkw 0xc9f4fa73f3ea4c58 0x8c9f4fa73f3ea4c5 0x01f0f871c3c00c01 0x101f0f871c3c00c0

def z1104 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xde0f078e3c3ff0f6 0x4de0f078e3c3ff0f

def z1105 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xc1ecc60fe338c0fb 0x7c1ecc60fe338c0f

def z1106 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xcfeffe0ffc3fc0f2 0x5cfeffe0ffc3fc0f

def z1107 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xeffffffffc3f300f 0xfeffffffffc3f300

def z1108 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x0ffff9ffc0000003 0x90ffff9ffc000000

def z1109 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0xd1fcfe7fe038c0ff 0x7d1fcfe7fe038c0f

def z1110 : W := mkw 0x8ddfb2ff80000000 0x08ddfb2ff8000000 0x01f3f871c0000001 0x101f3f871c000000

def z1111 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6feff8003fff000a 0x56feff8003fff000

def z1112 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ff3f8003fff0009 0x96ff3f8003fff000

def z1113 : W := mkw 0x4dbee8037bfe0450 0x84dbee8037bfe045 0x6ffff801ffff000b 0xf6ffff801ffff000

def z1114 : W := mkw 0x9fdfb7ff881510a3 0x09fdfb7ff881510a 0x8fffffffc0070007 0xf8fffffffc007000

def z1115 : W := mkw 0x224117fbc401ffde 0xc224117fbc401ffd 0x900007ffc000fff4 0x0900007ffc000fff

def z1116 : W := mkw 0x0b504f60416315c2 0x40b504f60416315c 0xbff007f003e73fcd 0xfbff007f003e73fc

def z1117 : W := mkw 0x04aec8002b7e0000 0x004aec8002b7e000 0x6ffff8003fff000b 0xf6ffff8003fff000

def z1118 : W := mkw 0x00c592db80011082 0x000c592db8001108 0xf1ffffffe03ff0ff 0xff1ffffffe03ff0f

def z1119 : W := mkw 0x09311098f28115c2 0x409311098f28115c 0x7ff001f9ffc03fcd 0xf7ff001f9ffc03fc

def z1120 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x2ffff8001fff0003 0x92ffff8001fff000

def z1121 : W := mkw 0x4dbea8003ade0000 0x04dbea8003ade000 0x6fff38003cff000a 0xf6fff38003cff000

def z1122 : W := mkw 0x8d9fb09f80000000 0x08d9fb09f8000000 0x0feff80fc0000002 0x50feff80fc000000

def z1123 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfffc07f03ff8ff0f 0xffffc07f03ff8ff0

def z1124 : W := mkw 0xafdfb7ff8400ea0c 0x0afdfb7ff8400ea0 0x8fffffffc000c007 0xf8fffffffc000c00

def z1125 : W := mkw 0x026007402600e808 0x0026007402600e80 0xfff007f03fc0ff0d 0xffff007f03fc0ff0

def z1126 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xc1ecc64fe038c0f7 0x7c1ecc64fe038c0f

def z1127 : W := mkw 0x9fdfb7ff8c14a021 0x09fdfb7ff8c14a02 0x8fffffffdc000007 0xf8fffffffdc00000

def z1128 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0xeffffe063fffc03b 0xfeffffe063fffc03

def z1129 : W := mkw 0x00e4824362084c58 0x800e4824362084c5 0xc1ec060fe018c0f0 0x5c1ec060fe018c0f

def z1130 : W := mkw 0x00e4ca43636a4c58 0x800e4ca43636a4c5 0xf1ecc64fe3ffccff 0x7f1ecc64fe3ffccf

def z1131 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8fffffbfc0000002 0xd8fffffbfc000000

def z1132 : W := mkw 0x8fdfb7ff8c14a000 0x08fdfb7ff8c14a00 0xfffffffffc3ff00f 0xffffffffffc3ff00

def z1133 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x01f0f879c0000007 0x301f0f879c000000

def z1134 : W := mkw 0x8f9fb59f80000000 0x08f9fb59f8000000 0x8fffff8fc0000007 0xf8fffff8fc000000

def z1135 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xcffffffffc3fc0f7 0xfcffffffffc3fc0f

def z1136 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xffefff8ffc3ff0fe 0xfffefff8ffc3ff0f

def z1137 : W := mkw 0x8fdfb7ff8401b082 0x08fdfb7ff8401b08 0xfffffffffc27f0cf 0xffffffffffc27f0c

def z1138 : W := mkw 0x402048007bff5dda 0xc402048007bff5dd 0x700000003ffffff8 0x0700000003ffffff

def z1139 : W := mkw 0x8994b01380000000 0x08994b0138000000 0x01f0f801c0000001 0x101f0f801c000000

def z1140 : W := mkw 0x8fdeb77780000000 0x08fdeb7778000000 0x0ff0f871c0000001 0x10ff0f871c000000

def z1141 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8fefffffc0000006 0x58fefffffc000000

def z1142 : W := mkw 0x44aee8002b7e0000 0x044aee8002b7e000 0x6feff8003f3f000b 0xf6feff8003f3f000

def z1143 : W := mkw 0xafdfb7ff8400ea0c 0x0afdfb7ff8400ea0 0xfffffffffc00ff0f 0xffffffffffc00ff0

def z1144 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0x7013f9f9e3ffffff 0xa7013f9f9e3fffff

def z1145 : W := mkw 0x09d4a24300000000 0x009d4a2430000000 0x01f0f841c0000001 0x101f0f841c000000

def z1146 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ff3f8003fc70009 0xf6ff3f8003fc7000

def z1147 : W := mkw 0xbfdfb7ff8401faaf 0x0bfdfb7ff8401faa 0x9fffffffc000fff7 0xf9fffffffc000fff

def z1148 : W := mkw 0x8d9eb01380000000 0x08d9eb0138000000 0x0ffff801c0000003 0xf0ffff801c000000

def z1149 : W := mkw 0x4dbee8033bfe0000 0x04dbee8033bfe000 0x6ffff80fffff000b 0xf6ffff80fffff000

def z1150 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x2ffff8001fc70003 0xf2ffff8001fc7000

def z1151 : W := mkw 0xafdfb7ff8400a204 0x0afdfb7ff8400a20 0x8fffffffc0003307 0xf8fffffffc000330

def z1152 : W := mkw 0x9fdfb7ff8c14a021 0x09fdfb7ff8c14a02 0xdffffffffc38c0ff 0xfdffffffffc38c0f

def z1153 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfffc07fe3fc0ff0f 0xffffc07fe3fc0ff0

def z1154 : W := mkw 0x8fdfb7ff80011182 0x48fdfb7ff8001118 0x8fffffffc0003307 0xf8fffffffc000330

def z1155 : W := mkw 0x00204800636b5dda 0xc00204800636b5dd 0x50000000233fccf8 0x050000000233fccf

def z1156 : W := mkw 0x00015898c16315c2 0x400015898c16315c 0xf013fff9e3e7ffcf 0xef013fff9e3e7ffc

def z1157 : W := mkw 0x8ddeb27388140000 0x08ddeb2738814000 0x6ffff871fc3f000b 0xf6ffff871fc3f000

def z1158 : W := mkw 0x8bd5b7ff80000000 0x08bd5b7ff8000000 0x81fcffffc0000007 0x781fcffffc000000

def z1159 : W := mkw 0x3f1b1dbc9cd7b3a7 0x43f1b1dbc9cd7b3a 0x2e1339b01cc73300 0x82e1339b01cc7330

def z1160 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1fffe4fe338ccff 0xfd1fffe4fe338ccf

def z1161 : W := mkw 0x9ddfb2ff881510a3 0x09ddfb2ff881510a 0x01fff87fc03f00f3 0x101fff87fc03f00f

def z1162 : W := mkw 0x548ff89cc97f15e3 0x4548ff89cc97f15e 0x000ff80fc03f00f2 0x0000ff80fc03f00f

def z1163 : W := mkw 0x84cfb2df80000000 0x084cfb2df8000000 0x01eff84fc0000003 0x101eff84fc000000

def z1164 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1fcc67fe3f8cfff 0x7d1fcc67fe3f8cff

def z1165 : W := mkw 0x493048003bfe0000 0x0493048003bfe000 0x6ff3f8003fff000b 0xf6ff3f8003fff000

def z1166 : W := mkw 0xabd4b7738400ea0c 0x0abd4b7738400ea0 0x91f0fff1c000ff05 0x191f0fff1c000ff0

def z1167 : W := mkw 0x9fdfb7ff8401b0a3 0x09fdfb7ff8401b0a 0xfffffffffc00f0ff 0xffffffffffc00f0f

def z1168 : W := mkw 0x8fdfb7ff88151082 0x08fdfb7ff8815108 0xfffffffffc3f30cf 0xffffffffffc3f30c

def z1169 : W := mkw 0x4dbee8007bfe0440 0x04dbee8007bfe044 0x6ffff809ffff00cb 0xf6ffff809ffff00c

def z1170 : W := mkw 0x8bd5b7fb80000000 0x08bd5b7fb8000000 0x8ff3fff9c0000007 0xf8ff3fff9c000000

def z1171 : W := mkw 0xabd4b7739480a204 0x0abd4b7739480a20 0x2ff0f9f1dcc03301 0x92ff0f9f1dcc0330

def z1172 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x01fcf871c0000003 0x701fcf871c000000

def z1173 : W := mkw 0x0b3005003680a000 0x00b3005003680a00 0xfff007f03fc0ff0d 0xffff007f03fc0ff0

def z1174 : W := mkw 0x8bd5b7ff80000000 0x08bd5b7ff8000000 0x81f3ffffc0000007 0xb81f3ffffc000000

def z1175 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1fcc7ffe338ccff 0xfd1fcc7ffe338ccf

def z1176 : W := mkw 0x9fdfb7ff8c15b0a3 0x09fdfb7ff8c15b0a 0xafffffffdc3f30f7 0xfafffffffdc3f30f

def z1177 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x31f0f9f1c3c03f0d 0xb31f0f9f1c3c03f0

def z1178 : W := mkw 0x8d9fb09f80000000 0x08d9fb09f8000000 0x0ffff9ffc0000007 0xf0ffff9ffc000000

def z1179 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xf1ecc64fe3f8ffff 0x7f1ecc64fe3f8fff

def z1180 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xbff007f01fc0ff05 0x9bff007f01fc0ff0

def z1181 : W := mkw 0x9fdfb7ff8401b0a3 0x09fdfb7ff8401b0a 0xdfffffffe038f0ff 0xfdfffffffe038f0f

def z1182 : W := mkw 0xbfdfb7ff9c95b2a7 0x0bfdfb7ff9c95b2a 0xafffffffdcc73307 0xfafffffffdcc7330

def z1183 : W := mkw 0x84cfb2df80000000 0x084cfb2df8000000 0x81effe0fc0000002 0x581effe0fc000000

def z1184 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6feff8003c3f000a 0xf6feff8003c3f000

def z1185 : W := mkw 0xafdfb7ff8400ea0c 0x0afdfb7ff8400ea0 0xbfffffffc3c0ff0f 0xfbfffffffc3c0ff0

def z1186 : W := mkw 0x120005000c15b0a3 0x0120005000c15b0a 0xfe0c078e3c3ff0fe 0xefe0c078e3c3ff0f

def z1187 : W := mkw 0x89d5b2fb80000000 0x089d5b2fb8000000 0x01f3f879c0000003 0x101f3f879c000000

def z1188 : W := mkw 0x160a05040c15b0a3 0x0160a05040c15b0a 0xfe0c07863c3ff0fc 0xefe0c07863c3ff0f

def z1189 : W := mkw 0x4020480073eb15c2 0x44020480073eb15c 0x3000000003e73fc8 0x03000000003e73fc

def z1190 : W := mkw 0x89d4b27380000000 0x089d4b2738000000 0x01f3f871c0000003 0xb01f3f871c000000

def z1191 : W := mkw 0x4dbee8007bfe4c58 0x84dbee8007bfe4c5 0xfffffe0e3fffccff 0xffffffe0e3fffccf

def z1192 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8feffe4fc0000007 0x78feffe4fc000000

def z1193 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0xafffffffc027000f 0xfafffffffc027000

def z1194 : W := mkw 0x0060424063204c48 0x00060424063204c4 0xd1ecc64fe338ccff 0x7d1ecc64fe338ccf

def z1195 : W := mkw 0x8b5117ff80000000 0x08b5117ff8000000 0x8ff3ffffc0000007 0xf8ff3ffffc000000

def z1196 : W := mkw 0x0001189880431182 0x4000118988043118 0x3013f9f9c3c73f0f 0xa3013f9f9c3c73f0

def z1197 : W := mkw 0x160b058c0c15b0a3 0x0160b058c0c15b0a 0xfe0f07863c3ff0f8 0xcfe0f07863c3ff0f

def z1198 : W := mkw 0x8fdfb7ff80000000 0x08fdfb7ff8000000 0x8ffcffffc0000005 0x58ffcffffc000000

def z1199 : W := mkw 0x140b008c081510a3 0x0140b008c081510a 0xfe0f060e3c3fc0fe 0xefe0f060e3c3fc0f

def z1200 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x7ffff8403fff0c0f 0xf7ffff8403fff0c0

def z1201 : W := mkw 0x8f9fb5bc80000000 0x08f9fb5bc8000000 0x0ffff9f9c0000007 0xf0ffff9f9c000000

def z1202 : W := mkw 0x8f9fb5bf80000000 0x08f9fb5bf8000000 0x0ffff9bfc0000003 0xf0ffff9bfc000000

def z1203 : W := mkw 0x00005810c1620540 0x400005810c162054 0x3013f9f1c3e73f0f 0xa3013f9f1c3e73f0

def z1204 : W := mkw 0x4d9ee80019f60000 0x04d9ee80019f6000 0x2ffff8001fe7000b 0xf2ffff8001fe7000

def z1205 : W := mkw 0x00e4c24363284c58 0x800e4c24363284c5 0xd1ecc60fe038c0fe 0x7d1ecc60fe038c0f

def z1206 : W := mkw 0x4dbee8003bfe0000 0x04dbee8003bfe000 0x6ffff9f03fff000f 0xf6ffff9f03fff000

def z1207 : W := mkw 0x6dbee8203bfe0204 0x06dbee8203bfe020 0x6ffff8303fff030b 0xf6ffff8303fff030

def z1208 : W := mkw 0x8fdfb7ff8400a000 0x08fdfb7ff8400a00 0xcffffffffc00c007 0xfcffffffffc00c00

def z1209 : W := mkw 0x8ddeb27380000000 0x08ddeb2738000000 0x0ffcf871c0000001 0x50ffcf871c000000

def z1210 : W := mkw 0x2b7007603680ea0c 0x02b7007603680ea0 0xfff0c7f9ffc0ff0f 0xffff0c7f9ffc0ff0

def z1211 : W := mkw 0x9f9fb59f8c15b0a3 0x09f9fb59f8c15b0a 0xffffff8ffc3ff0ff 0xfffffff8ffc3ff0f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z8,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z10,z11]),(0,[z1,z2,z3,z4,z5,z9,z12])],[(0,[z13,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z14,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z15,z5,z9]),(0,[z1,z2,z3,z4,z5,z16,z9]),(0,[z1,z2,z17,z3,z4,z5,z18]),(0,[z1,z19,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z20])],[(0,[z1,z2,z3,z4,z21,z5,z6]),(0,[z1,z22,z2,z3,z4,z5,z9]),(0,[z23,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z24,z9])],[(0,[z1,z25,z2,z3,z4,z5,z9]),(0,[z1,z26,z2,z3,z4,z5,z6]),(0,[z1,z2,z27,z3,z4,z5,z28])],[(0,[z1,z2,z3,z29,z30,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z31]),(0,[z32,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z33,z4,z5,z9]),(0,[z34,z1,z2,z3,z4,z5,z9]),(0,[z35,z1,z2,z3,z4,z5,z9])],[(0,[z36,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z37,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z38,z11]),(0,[z39,z40,z2,z3,z4,z5,z9]),(0,[z1,z41,z2,z3,z42,z5,z9]),(0,[z1,z2,z43,z3,z4,z5,z10]),(1,[z1,z2,z3,z4,z5,z44]),(0,[z1,z2,z45,z4,z5,z9,z11]),(0,[z1,z46,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z47,z5,z48])]],
   [[(0,[z1,z2,z3,z49,z4,z5,z9]),(0,[z50,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z51]),(0,[z52,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z53,z3,z4,z5,z9]),(0,[z34,z1,z54,z2,z3,z4,z5]),(0,[z1,z2,z55,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z56,z5,z9])],[(0,[z57,z1,z26,z3,z4,z5,z9]),(0,[z1,z2,z58,z3,z4,z5,z9]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z59,z5,z10]),(0,[z1,z60,z2,z3,z4,z5,z9])],[(0,[z1,z2,z61,z3,z5,z62,z9]),(0,[z1,z2,z3,z4,z5,z6,z63])],[(0,[z64,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z65,z5,z9]),(0,[z1,z66,z2,z67,z3,z4,z5]),(0,[z68,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z69,z4,z5,z9]),(0,[z1,z2,z3,z70,z4,z5,z9]),(0,[z1,z2,z3,z4,z71,z5,z9])],[(1,[z1,z2,z3,z4,z5,z9]),(1,[z1,z72,z73,z4,z5,z9]),(0,[z1,z2,z3,z74,z4,z5,z9])],[(0,[z1,z2,z75,z3,z4,z5,z11]),(0,[z1,z76,z2,z3,z4,z5,z9]),(0,[z77,z1,z2,z3,z4,z5,z9]),(0,[z1,z54,z2,z3,z4,z5,z12]),(1,[z1,z2,z78,z70,z5,z9]),(0,[z1,z2,z3,z4,z5,z79,z9])],[(0,[z1,z2,z3,z80,z4,z5,z9]),(0,[z1,z81,z3,z4,z42,z5,z9]),(0,[z1,z2,z3,z82,z4,z5,z9]),(0,[z83,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z84])]],
   [[(0,[z1,z85,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z70,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z11,z86])],[(0,[z1,z2,z3,z4,z87,z5,z9]),(0,[z1,z2,z88,z3,z4,z5,z9]),(0,[z1,z54,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z67,z3,z4,z5,z89])],[(0,[z1,z2,z3,z4,z5,z90,z9]),(0,[z1,z2,z3,z4,z5,z91,z9]),(0,[z1,z2,z3,z4,z5,z9,z92]),(0,[z1,z2,z3,z4,z93,z5,z9]),(0,[z1,z2,z3,z4,z5,z94,z9])],[(0,[z1,z2,z95,z3,z4,z96,z5]),(0,[z1,z2,z97,z3,z4,z5,z9]),(0,[z1,z98,z3,z4,z5,z10,z9])],[(0,[z1,z2,z3,z4,z5,z9,z99]),(0,[z1,z2,z100,z3,z4,z5,z9]),(0,[z1,z2,z3,z101,z4,z5,z9]),(0,[z1,z2,z3,z102,z4,z5,z11])],[(0,[z1,z2,z103,z3,z4,z5,z9]),(0,[z1,z66,z73,z3,z4,z5,z9])],[(1,[z1,z25,z2,z3,z4,z5]),(0,[z1,z2,z104,z3,z4,z5,z9]),(0,[z1,z2,z105,z3,z5,z9,z12])],[(0,[z106,z57,z2,z3,z4,z5,z9]),(0,[z0,z1,z2,z107,z4,z5,z9]),(0,[z1,z2,z3,z4,z108,z5,z9]),(0,[z1,z2,z3,z4,z5,z109,z11])]],
   [[(0,[z1,z81,z41,z3,z4,z5,z9]),(0,[z110,z1,z2,z3,z4,z5,z9])],[(0,[z111,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z107,z4,z5,z11]),(0,[z1,z112,z2,z3,z4,z5,z9]),(0,[z1,z2,z17,z3,z4,z113,z9]),(0,[z1,z2,z3,z4,z47,z5,z11]),(0,[z1,z114,z2,z3,z4,z5,z9]),(0,[z1,z115,z2,z3,z4,z5,z9])],[(0,[z0,z2,z75,z3,z4,z5,z9]),(0,[z1,z2,z3,z3,z4,z5,z9]),(0,[z1,z2,z3,z116,z4,z5,z11]),(0,[z1,z2,z61,z3,z4,z5,z9]),(0,[z1,z2,z3,z117,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z118,z9]),(0,[z1,z2,z119,z3,z4,z5,z9]),(0,[z1,z120,z2,z3,z4,z5,z9]),(0,[z121,z1,z2,z3,z4,z5,z9])],[(1,[z1,z122,z3,z4,z5,z9]),(0,[z34,z1,z2,z123,z4,z5,z9]),(0,[z1,z98,z2,z3,z4,z5,z9]),(0,[z124,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z125,z3,z4,z5,z9])],[(0,[z1,z2,z126,z3,z4,z5,z9]),(0,[z1,z127,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z128]),(0,[z1,z2,z3,z129,z4,z5,z9]),(0,[z1,z2,z3,z130,z4,z5,z11]),(0,[z110,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z107,z4,z5,z9,z11]),(1,[z1,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z4,z132,z5,z9]),(0,[z1,z2,z17,z4,z133,z5,z9])],[(0,[z1,z2,z3,z4,z134,z5,z9]),(0,[z135,z1,z2,z3,z4,z5,z9]),(1,[z39,z1,z136,z4,z5,z9]),(0,[z1,z81,z2,z3,z29,z5,z9]),(1,[z1,z2,z3,z4,z5,z137]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z118,z6])],[(1,[z138,z2,z3,z4,z21,z9]),(0,[z1,z98,z2,z3,z4,z5,z6]),(0,[z1,z139,z2,z3,z4,z5,z9])]],
   [[(0,[z140,z2,z3,z4,z96,z5,z9])],[(0,[z141,z1,z2,z3,z142,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z143]),(0,[z1,z2,z3,z4,z144,z145,z9]),(0,[z1,z2,z27,z78,z4,z5,z9]),(0,[z1,z2,z146,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z147,z9])],[(0,[z1,z2,z3,z4,z148,z5,z9]),(1,[z1,z2,z123,z4,z5,z9]),(0,[z1,z66,z2,z3,z4,z47,z5]),(0,[z1,z2,z3,z4,z5,z9,z149]),(1,[z1,z2,z150,z3,z4,z11]),(0,[z1,z2,z151,z3,z4,z5,z9])],[(1,[z1,z2,z3,z152,z4,z9]),(0,[z1,z2,z3,z4,z153,z5,z9]),(0,[z1,z66,z2,z3,z4,z5,z89]),(0,[z1,z54,z2,z3,z4,z5,z63]),(0,[z1,z2,z3,z4,z30,z5,z9])],[(0,[z1,z2,z3,z4,z154,z5,z9]),(1,[z1,z2,z3,z155,z5,z9]),(0,[z156,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z157]),(0,[z1,z2,z3,z4,z5,z158,z9])],[(0,[z1,z2,z159,z3,z4,z5,z9]),(0,[z140,z1,z2,z160,z4,z5,z9]),(1,[z140,z2,z3,z96,z5,z9]),(0,[z1,z2,z3,z4,z5,z161,z9]),(0,[z1,z2,z162,z3,z4,z5,z9]),(0,[z1,z2,z73,z3,z4,z5,z163]),(1,[z1,z54,z3,z4,z5,z24]),(0,[z1,z2,z3,z164,z4,z5,z9]),(0,[z1,z2,z67,z17,z3,z4,z9]),(0,[z1,z2,z3,z4,z165,z5,z9]),(0,[z166,z1,z2,z3,z4,z5,z11]),(1,[z1,z2,z3,z4,z167,z11]),(0,[z1,z2,z67,z3,z4,z47,z9]),(0,[z1,z2,z168,z3,z4,z5,z9])],[(0,[z169,z1,z2,z3,z4,z5,z9]),(0,[z39,z1,z2,z3,z117,z5,z9]),(0,[z1,z41,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z170,z9])],[(0,[z106,z1,z2,z3,z4,z171,z9]),(0,[z1,z2,z3,z172,z4,z5,z9]),(0,[z1,z2,z3,z4,z30,z5,z6]),(0,[z1,z2,z3,z4,z5,z89,z11]),(0,[z1,z2,z3,z4,z5,z173,z9])]],
   [[(0,[z1,z2,z174,z3,z4,z5,z9]),(0,[z1,z2,z175,z3,z4,z5,z9]),(0,[z1,z2,z176,z3,z4,z5,z9])],[(0,[z177,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z178,z3,z4,z5,z9]),(0,[z39,z1,z2,z179,z4,z5,z9]),(0,[z1,z2,z180,z3,z4,z5,z9]),(0,[z1,z2,z181,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z182,z9]),(0,[z1,z54,z2,z3,z4,z182,z9]),(0,[z1,z2,z3,z4,z183,z5,z9]),(0,[z1,z2,z184,z3,z4,z5,z9])],[(0,[z185,z2,z3,z107,z4,z5,z9]),(0,[z141,z1,z2,z3,z4,z5,z9]),(0,[z141,z1,z2,z3,z96,z5,z9]),(0,[z1,z2,z3,z4,z186,z5,z9]),(0,[z1,z41,z2,z3,z4,z5,z6]),(0,[z1,z2,z187,z3,z4,z5,z9]),(0,[z1,z2,z67,z3,z4,z5,z145])],[(0,[z188,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z152,z4,z96,z9]),(0,[z7,z138,z2,z3,z4,z5,z9]),(0,[z1,z2,z189,z3,z4,z5,z9]),(0,[z1,z2,z67,z3,z4,z5,z12])],[(0,[z190,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z89,z38]),(0,[z1,z2,z191,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z192,z5,z9])],[(0,[z1,z193,z2,z3,z4,z5,z9]),(0,[z1,z72,z2,z73,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z194,z9]),(0,[z1,z2,z3,z4,z5,z195,z9])],[(0,[z141,z1,z2,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z4,z5,z9]),(1,[z7,z2,z3,z4,z62,z9]),(0,[z1,z2,z3,z4,z196,z5,z9])],[(0,[z106,z1,z2,z3,z4,z5,z9]),(0,[z185,z1,z2,z3,z4,z5,z197]),(0,[z1,z198,z2,z3,z4,z5,z9]),(0,[z0,z1,z2,z199,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z200]),(0,[z1,z201,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z202]),(0,[z1,z2,z203,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z204,z5,z9])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z11]),(0,[z205,z1,z2,z3,z4,z5,z9]),(0,[z1,z206,z2,z3,z4,z5,z9]),(0,[z1,z2,z207,z3,z4,z5,z9]),(0,[z1,z2,z208,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z209,z9]),(0,[z1,z2,z3,z4,z5,z6,z210]),(0,[z1,z211,z2,z3,z4,z5,z9]),(0,[z1,z2,z78,z3,z30,z5,z9])],[(0,[z1,z2,z212,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z213,z9]),(0,[z138,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z21,z5,z11]),(0,[z214,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z215,z3,z4,z5,z9])],[(0,[z106,z1,z2,z3,z4,z5,z6]),(0,[z1,z26,z2,z3,z4,z5,z11]),(0,[z216,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z63,z11]),(0,[z1,z2,z217,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z145,z9,z48])],[(0,[z1,z218,z75,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z219]),(0,[z1,z2,z3,z4,z220,z5,z9]),(0,[z221,z1,z2,z67,z3,z4,z5]),(0,[z1,z2,z3,z136,z4,z5,z9]),(0,[z1,z2,z3,z222,z4,z5,z9]),(1,[z1,z41,z3,z29,z5,z9]),(0,[z1,z2,z3,z223,z4,z5,z9]),(0,[z1,z224,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z107,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z225]),(0,[z1,z2,z3,z4,z5,z226,z9])],[(0,[z1,z2,z3,z227,z4,z5,z9]),(0,[z1,z2,z228,z3,z4,z5,z9]),(0,[z221,z34,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z229,z5,z9]),(0,[z1,z54,z2,z3,z4,z47,z5]),(0,[z1,z2,z3,z4,z5,z24,z11]),(0,[z1,z2,z3,z230,z4,z5,z9])],[(0,[z140,z1,z2,z3,z142,z5,z9]),(0,[z39,z1,z2,z3,z4,z5,z9]),(0,[z231,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z232,z9])]],
   [[(0,[z1,z2,z233,z3,z4,z5,z9]),(0,[z1,z2,z3,z136,z4,z5,z6]),(0,[z1,z234,z2,z3,z4,z5,z9]),(0,[z1,z2,z27,z3,z30,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z9]),(0,[z1,z2,z3,z235,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z236])],[(0,[z1,z2,z3,z4,z5,z237,z9]),(0,[z1,z2,z3,z4,z5,z9,z238])],[(0,[z1,z2,z3,z4,z5,z239,z9]),(0,[z1,z2,z240,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z11,z241]),(0,[z242,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z243,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z210]),(0,[z39,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z244]),(0,[z1,z54,z3,z4,z5,z24,z9]),(0,[z1,z2,z3,z4,z5,z245,z9]),(0,[z1,z2,z78,z3,z70,z5,z9]),(0,[z1,z46,z2,z3,z4,z5,z11])],[(0,[z1,z2,z3,z4,z246,z5,z9]),(0,[z1,z25,z2,z75,z3,z4,z5]),(0,[z1,z66,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z247,z9]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z248,z4,z5,z9])],[(0,[z1,z2,z45,z249,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z250,z9])],[(0,[z1,z2,z3,z4,z5,z210,z12]),(0,[z1,z251,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z252,z9]),(0,[z1,z41,z2,z3,z4,z170,z9]),(0,[z1,z2,z3,z4,z133,z5,z9]),(0,[z1,z2,z3,z130,z5,z89,z9])]],
   [[(0,[z253,z1,z2,z3,z4,z5,z9]),(0,[z140,z1,z2,z3,z4,z5,z9]),(0,[z1,z66,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z70,z4,z5,z11]),(0,[z1,z2,z254,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z247,z6]),(0,[z1,z2,z255,z3,z4,z5,z9])],[(0,[z57,z1,z75,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z197,z9]),(0,[z1,z2,z3,z4,z5,z202,z9]),(0,[z1,z2,z3,z4,z5,z9,z256]),(1,[z1,z2,z3,z4,z5,z11])],[(0,[z1,z2,z3,z257,z4,z5,z9]),(0,[z138,z1,z2,z3,z4,z62,z9]),(1,[z1,z2,z258,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z9]),(0,[z34,z1,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z259,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z260,z9]),(0,[z1,z2,z3,z4,z5,z261,z9])],[(0,[z262,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z263,z5,z9]),(0,[z1,z2,z179,z3,z4,z5,z149]),(0,[z1,z2,z3,z4,z133,z5,z6])],[(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z264,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z254,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z265])],[(0,[z266,z1,z2,z3,z4,z5,z9])],[(0,[z2,z199,z3,z107,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z267,z9]),(0,[z1,z2,z3,z268,z142,z5,z9]),(0,[z1,z2,z3,z269,z4,z5,z9])],[(0,[z1,z270,z2,z3,z4,z5,z9]),(0,[z1,z2,z199,z3,z4,z5,z9]),(0,[z2,z3,z4,z5,z38,z9,z210]),(0,[z1,z2,z271,z3,z4,z5,z9]),(0,[z1,z81,z2,z3,z42,z5,z9])]],
   [[(0,[z1,z2,z272,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z273]),(0,[z1,z274,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z275,z4,z5,z9])],[(0,[z276,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z277,z5]),(1,[z1,z66,z3,z4,z5,z63])],[(0,[z1,z2,z3,z4,z5,z278,z9]),(0,[z221,z1,z2,z3,z4,z47,z5]),(0,[z1,z2,z3,z4,z10,z145,z9])],[(0,[z1,z2,z199,z3,z4,z5,z6]),(0,[z1,z2,z279,z3,z4,z5,z9])],[(0,[z1,z2,z4,z133,z5,z113,z9]),(0,[z1,z2,z17,z3,z4,z5,z137]),(1,[z1,z2,z45,z4,z5,z11]),(0,[z1,z280,z2,z3,z4,z5,z9]),(0,[z1,z2,z281,z3,z4,z5,z9])],[(0,[z106,z2,z75,z3,z4,z5,z9]),(0,[z1,z282,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z283,z4,z5,z9]),(0,[z1,z2,z284,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z285])],[(0,[z1,z2,z3,z4,z5,z286,z9]),(0,[z40,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z287,z9]),(0,[z1,z2,z3,z3,z4,z5,z11])],[(0,[z288,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z258,z4,z5,z9]),(0,[z34,z1,z2,z105,z3,z4,z5]),(0,[z1,z2,z3,z289,z4,z5,z9]),(0,[z1,z98,z2,z3,z4,z5,z11])]],
   [[(0,[z1,z2,z199,z4,z30,z5,z9]),(0,[z1,z2,z3,z290,z4,z5,z9]),(0,[z1,z2,z3,z291,z4,z5,z9]),(0,[z7,z1,z2,z3,z4,z62,z9]),(0,[z7,z2,z3,z4,z5,z62,z9]),(0,[z1,z2,z3,z4,z5,z292,z9]),(0,[z1,z54,z2,z3,z4,z5,z9]),(0,[z1,z2,z281,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z142,z5,z9])],[(1,[z1,z2,z174,z3,z4,z9]),(0,[z1,z293,z2,z3,z4,z5,z9]),(0,[z294,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z21,z10,z9]),(0,[z1,z2,z3,z4,z295,z5,z9]),(0,[z39,z1,z2,z136,z4,z5,z9]),(0,[z1,z2,z179,z17,z4,z5,z9])],[(0,[z1,z2,z296,z3,z4,z5,z9]),(0,[z138,z1,z2,z3,z268,z4,z9]),(0,[z1,z2,z3,z4,z5,z9,z297]),(0,[z1,z66,z2,z3,z4,z5,z63]),(0,[z1,z2,z3,z4,z5,z298,z9])],[(0,[z1,z2,z3,z299,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z300,z9]),(0,[z1,z2,z3,z4,z301,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z167]),(0,[z1,z2,z3,z268,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z302])],[(0,[z1,z2,z3,z4,z5,z9,z303]),(0,[z1,z2,z3,z4,z304,z5,z9]),(0,[z141,z2,z3,z116,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z305]),(0,[z1,z2,z3,z4,z142,z5,z6]),(0,[z1,z2,z3,z4,z306,z5,z9]),(0,[z1,z307,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z308,z9]),(0,[z309,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z310,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z311,z9]),(0,[z1,z2,z312,z3,z4,z5,z9]),(1,[z1,z2,z95,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z313]),(0,[z1,z72,z73,z3,z4,z5,z9]),(1,[z1,z218,z3,z4,z144,z9]),(0,[z1,z2,z105,z3,z4,z5,z89])],[(0,[z1,z2,z314,z3,z4,z5,z9]),(0,[z1,z2,z3,z315,z4,z5,z9]),(0,[z1,z2,z3,z4,z182,z5,z9]),(0,[z1,z2,z3,z4,z30,z5,z11]),(0,[z1,z2,z3,z4,z5,z300,z6])]],
   [[(0,[z316,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z317,z3,z4,z5,z9]),(0,[z1,z2,z318,z3,z4,z5,z9]),(0,[z1,z2,z3,z319,z4,z5,z9]),(0,[z1,z320,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z63]),(0,[z1,z2,z3,z4,z5,z11,z12])],[(0,[z1,z2,z3,z4,z96,z5,z9]),(0,[z1,z2,z321,z3,z4,z5,z9]),(0,[z1,z2,z322,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z323,z5,z9]),(0,[z1,z2,z3,z324,z4,z5,z9]),(0,[z1,z41,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z6,z48])],[(0,[z1,z2,z3,z4,z325,z5,z9])],[(0,[z39,z1,z2,z4,z133,z5,z9]),(0,[z326,z1,z2,z3,z4,z5,z9])],[(1,[z0,z2,z199,z4,z5,z9]),(0,[z140,z1,z2,z3,z4,z5,z327]),(0,[z1,z2,z3,z4,z96,z5,z6]),(0,[z1,z2,z3,z4,z144,z5,z9])],[(0,[z328,z1,z2,z3,z4,z5,z9]),(0,[z39,z329,z2,z3,z4,z5,z9]),(0,[z1,z2,z179,z3,z4,z5,z51]),(0,[z330,z1,z2,z3,z4,z5,z9])],[(0,[z331,z1,z2,z3,z4,z5,z9]),(0,[z1,z332,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z333]),(1,[z1,z2,z3,z4,z5,z28]),(1,[z1,z2,z4,z5,z6,z11]),(0,[z1,z2,z150,z3,z4,z9,z11]),(0,[z1,z2,z3,z4,z5,z334,z9])]],
   [[(1,[z1,z2,z43,z3,z4,z5]),(1,[z1,z2,z249,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z335,z9]),(0,[z1,z2,z3,z4,z144,z5,z6])],[(0,[z336,z1,z2,z3,z4,z5,z9]),(0,[z138,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z337,z3,z4,z5,z9]),(0,[z1,z2,z150,z3,z4,z5,z9])],[(0,[z106,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z4,z338,z5,z10,z9]),(0,[z1,z2,z179,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z339])],[(0,[z1,z2,z3,z4,z5,z9,z200]),(0,[z140,z1,z2,z3,z4,z340,z9]),(0,[z341,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z142,z62,z9]),(0,[z221,z1,z2,z3,z4,z5,z9]),(0,[z39,z1,z2,z3,z4,z342,z9]),(0,[z343,z1,z2,z3,z4,z5,z9]),(0,[z1,z54,z2,z3,z4,z5,z24]),(0,[z1,z2,z207,z3,z4,z5,z11]),(1,[z1,z46,z3,z4,z5,z9]),(0,[z1,z344,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z48])],[(0,[z1,z2,z345,z3,z4,z5,z9]),(0,[z1,z26,z3,z4,z42,z5,z9]),(0,[z39,z1,z3,z4,z5,z24,z9]),(0,[z1,z2,z70,z4,z30,z5,z9]),(0,[z1,z2,z281,z3,z4,z142,z9]),(0,[z1,z2,z3,z5,z89,z9,z12])],[(0,[z1,z2,z3,z346,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z347]),(0,[z1,z81,z2,z3,z4,z5,z9]),(0,[z1,z2,z348,z4,z5,z10,z9]),(0,[z1,z46,z3,z4,z5,z9,z11]),(0,[z1,z2,z281,z3,z268,z5,z9]),(0,[z1,z2,z3,z4,z47,z145,z9])],[(0,[z140,z1,z2,z3,z4,z5,z219]),(0,[z221,z1,z54,z2,z3,z4,z5]),(0,[z1,z2,z179,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z21,z109,z9]),(0,[z221,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z136,z4,z5,z11]),(0,[z349,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z268,z4,z142,z9])],[(0,[z1,z2,z3,z107,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z9,z219]),(0,[z350,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z351,z3,z4,z5,z9])],[(0,[z352,z1,z2,z3,z4,z5,z9]),(0,[z1,z81,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z353])],[(0,[z1,z2,z354,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z355]),(1,[z1,z2,z3,z4,z356,z9]),(0,[z1,z2,z3,z357,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z11])],[(0,[z1,z2,z3,z358,z4,z5,z9]),(0,[z1,z359,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z360,z9]),(1,[z1,z2,z3,z4,z186,z9]),(0,[z361,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z339]),(0,[z362,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z363,z5,z9]),(0,[z1,z2,z67,z3,z4,z5,z9])],[(0,[z1,z2,z3,z364,z5,z62,z9]),(0,[z34,z1,z66,z2,z3,z4,z5]),(0,[z1,z2,z73,z3,z4,z5,z6]),(0,[z1,z2,z3,z42,z30,z5,z9]),(0,[z1,z98,z2,z3,z4,z10,z9]),(0,[z1,z2,z365,z3,z4,z5,z9]),(0,[z1,z2,z366,z3,z4,z5,z9])],[(0,[z140,z1,z2,z317,z4,z5,z9]),(0,[z1,z72,z2,z179,z4,z5,z9]),(0,[z1,z2,z367,z3,z4,z5,z9]),(0,[z1,z2,z17,z3,z4,z5,z11])]],
   [[(0,[z1,z2,z368,z3,z4,z5,z9]),(0,[z1,z2,z369,z3,z4,z5,z9]),(1,[z221,z2,z3,z4,z5,z38]),(0,[z370,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z371,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z372,z9]),(0,[z1,z2,z3,z4,z5,z9,z244]),(0,[z1,z66,z2,z3,z4,z5,z11]),(0,[z1,z373,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z374,z4,z5,z9]),(0,[z1,z2,z105,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z171,z9]),(0,[z1,z2,z375,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z144,z62,z9]),(0,[z34,z1,z2,z3,z130,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z38]),(0,[z1,z218,z2,z3,z4,z5,z9]),(0,[z1,z98,z2,z3,z4,z144,z9]),(0,[z1,z2,z3,z4,z5,z145,z11]),(0,[z1,z376,z2,z3,z4,z5,z6]),(0,[z1,z2,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z377,z9]),(0,[z1,z2,z3,z4,z5,z378,z9])],[(0,[z1,z2,z3,z379,z4,z5,z9]),(0,[z1,z380,z2,z3,z4,z5,z9])],[(0,[z140,z1,z37,z3,z4,z5,z9]),(0,[z1,z2,z381,z3,z4,z5,z9]),(1,[z1,z2,z61,z3,z5,z9]),(0,[z1,z382,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z383,z4,z5,z9]),(0,[z1,z384,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z133,z5,z11])],[(1,[z1,z2,z199,z4,z5,z11]),(0,[z140,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z9,z385]),(0,[z1,z2,z3,z386,z4,z5,z9]),(0,[z1,z2,z3,z374,z4,z5,z6])],[(0,[z1,z218,z2,z3,z4,z5,z6])],[(0,[z1,z54,z66,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z11])],[(0,[z1,z2,z387,z3,z4,z5,z9]),(1,[z1,z2,z17,z4,z133,z9])]],
   [[(0,[z1,z2,z3,z4,z388,z5,z9])],[(0,[z1,z2,z3,z4,z5,z5,z9])],[(0,[z389,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z390,z5,z9])],[(0,[z391,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z199,z3,z4,z5,z11]),(0,[z221,z2,z3,z4,z5,z38,z9]),(0,[z1,z73,z3,z4,z5,z24,z9]),(1,[z1,z2,z348,z4,z5,z9])],[(0,[z1,z392,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z393,z4,z5,z9]),(1,[z1,z2,z3,z4,z394,z9]),(0,[z1,z2,z3,z4,z5,z395,z9]),(0,[z396,z1,z2,z3,z4,z5,z9])],[(1,[z1,z2,z3,z397,z4,z5]),(0,[z34,z1,z2,z3,z4,z5,z11]),(0,[z1,z72,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z29,z4,z5,z9]),(0,[z1,z2,z3,z4,z42,z5,z9]),(0,[z1,z2,z3,z4,z5,z398,z9])],[(0,[z57,z1,z2,z3,z4,z5,z9]),(0,[z34,z1,z2,z258,z4,z5,z9]),(0,[z1,z2,z3,z4,z144,z113,z9]),(0,[z1,z2,z399,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z400,z9]),(0,[z1,z2,z3,z4,z401,z5,z9]),(0,[z1,z2,z3,z4,z5,z402,z9]),(0,[z7,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z403,z9]),(0,[z1,z2,z404,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z405,z5,z9]),(0,[z1,z2,z3,z4,z406,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z407,z5,z9]),(0,[z1,z408,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z409,z9]),(0,[z1,z2,z281,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z410,z9])],[(1,[z57,z26,z3,z4,z5,z9]),(0,[z411,z1,z2,z3,z4,z5,z9]),(0,[z1,z72,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z42,z5,z6]),(0,[z1,z412,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z70,z29,z5,z9]),(0,[z1,z2,z3,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z413,z5,z9])],[(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z78,z107,z4,z5,z9]),(0,[z1,z2,z3,z397,z4,z96,z5]),(0,[z34,z1,z2,z3,z4,z5,z38]),(0,[z414,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z415,z4,z5,z9]),(1,[z1,z2,z3,z4,z47,z145])],[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z268,z4,z5,z173])],[(0,[z1,z2,z3,z4,z5,z416,z9]),(0,[z417,z1,z2,z3,z4,z5,z9]),(0,[z1,z54,z2,z3,z4,z5,z11]),(0,[z1,z2,z179,z3,z4,z113,z9]),(0,[z1,z2,z3,z4,z5,z18,z9]),(0,[z1,z2,z3,z4,z5,z9,z418])],[(0,[z1,z2,z3,z4,z364,z5,z9]),(0,[z1,z419,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z163]),(0,[z1,z2,z27,z3,z70,z5,z9]),(0,[z1,z2,z420,z3,z4,z5,z9])],[(0,[z1,z2,z3,z421,z4,z5,z9]),(0,[z1,z2,z3,z422,z4,z5,z9]),(0,[z1,z122,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z423]),(0,[z1,z2,z424,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z425,z9]),(0,[z1,z426,z2,z3,z4,z5,z9])],[(0,[z1,z2,z107,z4,z30,z5,z9]),(0,[z1,z2,z3,z4,z5,z427,z9]),(0,[z1,z2,z3,z4,z5,z428,z9]),(0,[z429,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z430,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z84])]],
   [[(0,[z2,z75,z3,z107,z4,z5,z9]),(0,[z1,z2,z3,z431,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z432])],[(0,[z433,z1,z2,z3,z4,z5,z9]),(0,[z434,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z59,z5]),(0,[z309,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z435,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z47,z5,z89])],[(0,[z39,z1,z2,z3,z4,z5,z131]),(0,[z1,z436,z2,z3,z4,z5,z9])],[(1,[z1,z2,z3,z4,z5,z197]),(0,[z1,z2,z43,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z437,z5,z9]),(0,[z1,z2,z3,z4,z5,z427,z6])],[(0,[z1,z2,z78,z3,z4,z5,z157]),(0,[z316,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z438,z11]),(0,[z1,z2,z3,z130,z4,z5,z89])],[(0,[z1,z2,z3,z4,z96,z5,z11]),(0,[z7,z1,z122,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z62,z9])],[(1,[z1,z8,z3,z4,z5,z9]),(0,[z1,z2,z3,z439,z4,z5,z9]),(0,[z1,z2,z73,z3,z4,z5,z347]),(0,[z1,z2,z3,z4,z59,z5,z9]),(0,[z1,z440,z2,z3,z4,z5,z9])],[(0,[z1,z2,z441,z3,z4,z5,z9]),(0,[z1,z2,z442,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z24]),(0,[z443,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z67,z3,z4,z5,z48]),(0,[z1,z2,z3,z4,z5,z9,z444])]],
   [[(0,[z1,z2,z3,z4,z445,z5,z9])],[(0,[z1,z2,z446,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z447,z9]),(0,[z141,z1,z2,z281,z3,z5,z9]),(0,[z1,z2,z3,z4,z5,z62,z6]),(0,[z1,z2,z3,z4,z5,z38,z12]),(0,[z39,z1,z2,z3,z155,z5,z9]),(0,[z1,z2,z3,z4,z144,z5,z11]),(0,[z1,z2,z3,z4,z5,z11,z238]),(0,[z1,z2,z3,z4,z5,z167,z11])],[(0,[z1,z2,z448,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z449,z5,z9]),(0,[z1,z2,z3,z4,z133,z10,z9]),(0,[z1,z2,z3,z268,z4,z5,z9])],[(1,[z1,z2,z3,z4,z5,z237]),(0,[z450,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z451,z9]),(0,[z1,z66,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z452,z9]),(0,[z1,z2,z281,z3,z5,z109,z9])],[(0,[z1,z2,z3,z4,z5,z453,z9]),(0,[z138,z1,z2,z3,z4,z21,z9]),(0,[z1,z2,z3,z4,z5,z9,z28]),(0,[z454,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z455,z9]),(0,[z1,z2,z3,z456,z4,z5,z9]),(0,[z1,z2,z3,z268,z4,z5,z84]),(0,[z1,z2,z3,z4,z5,z457,z9])],[(0,[z1,z2,z3,z4,z5,z458,z9]),(0,[z459,z1,z2,z3,z4,z5,z9]),(1,[z34,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z4,z5,z9,z131]),(0,[z1,z2,z3,z4,z133,z144,z9])],[(0,[z1,z2,z3,z4,z5,z9,z137]),(0,[z1,z2,z150,z3,z4,z5,z11])],[(0,[z1,z2,z460,z3,z4,z5,z9]),(0,[z39,z1,z3,z136,z4,z5,z9]),(0,[z1,z72,z2,z136,z4,z5,z9]),(1,[z1,z98,z3,z4,z10,z9]),(0,[z1,z2,z3,z4,z5,z9,z461]),(0,[z1,z2,z179,z3,z4,z5,z11])]],
   [[(1,[z1,z462,z3,z4,z5,z9]),(0,[z1,z2,z8,z3,z4,z5,z9]),(0,[z1,z2,z463,z3,z4,z5,z9]),(0,[z1,z2,z3,z464,z4,z5,z9]),(1,[z1,z46,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z9,z465])],[(0,[z1,z2,z466,z3,z4,z5,z9]),(0,[z1,z2,z467,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z468,z5,z9]),(0,[z1,z2,z3,z4,z5,z469,z9]),(0,[z459,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z105,z3,z5,z12])],[(0,[z1,z2,z3,z4,z470,z5,z9]),(0,[z1,z471,z2,z3,z4,z5,z9]),(0,[z1,z472,z2,z3,z4,z5,z9]),(1,[z40,z2,z3,z4,z5,z9]),(0,[z1,z81,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z113,z9]),(0,[z473,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z75,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z29,z5,z9]),(0,[z1,z2,z3,z474,z4,z5,z9]),(0,[z1,z2,z475,z3,z4,z5,z9]),(1,[z1,z2,z281,z3,z109,z9]),(0,[z1,z2,z67,z3,z4,z9,z48])],[(0,[z1,z2,z3,z4,z476,z5,z9]),(0,[z1,z2,z3,z4,z4,z5,z9]),(1,[z141,z2,z3,z116,z5,z9]),(0,[z477,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z78,z70,z4,z5,z9]),(0,[z1,z2,z478,z3,z4,z5,z9])],[(0,[z479,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z480,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z481,z9])],[(0,[z1,z2,z3,z4,z5,z9,z482]),(0,[z483,z1,z2,z3,z4,z5,z9]),(0,[z140,z141,z2,z3,z4,z5,z9]),(0,[z141,z1,z2,z3,z116,z5,z9]),(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z1,z2,z3,z4,z5,z484,z9])],[(0,[z1,z2,z3,z4,z5,z9,z485]),(0,[z1,z2,z3,z4,z5,z486,z9]),(0,[z1,z2,z281,z3,z4,z10,z9])]],
   [[(0,[z1,z2,z3,z487,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z488]),(0,[z1,z2,z489,z3,z4,z5,z9]),(0,[z221,z1,z2,z3,z4,z5,z210]),(0,[z1,z329,z2,z3,z4,z5,z9]),(0,[z39,z1,z66,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z490,z9]),(0,[z1,z2,z3,z4,z491,z5,z9]),(0,[z1,z2,z492,z3,z4,z5,z9])],[(1,[z106,z75,z3,z4,z5,z9]),(0,[z141,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z67,z3,z4,z5,z11]),(1,[z1,z2,z3,z130,z5,z89])],[(0,[z7,z1,z2,z3,z4,z21,z9]),(0,[z1,z493,z2,z3,z4,z5,z9]),(0,[z1,z72,z2,z4,z133,z5,z9]),(0,[z1,z2,z281,z3,z4,z144,z9]),(0,[z1,z2,z494,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z47,z5,z145])],[(0,[z1,z2,z3,z116,z4,z5,z9]),(0,[z7,z1,z2,z3,z268,z4,z9]),(1,[z1,z2,z3,z4,z298,z9]),(0,[z1,z2,z3,z4,z47,z5,z12])],[(0,[z1,z495,z2,z3,z4,z5,z9]),(0,[z1,z2,z496,z3,z4,z5,z62]),(0,[z1,z2,z3,z4,z5,z313,z9]),(0,[z497,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z78,z3,z4,z5,z44])],[(0,[z498,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z174,z3,z4,z96,z9]),(0,[z1,z2,z123,z3,z4,z5,z9]),(0,[z1,z218,z2,z3,z4,z5,z11])],[(0,[z499,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z342,z9]),(0,[z1,z2,z3,z130,z4,z5,z12])],[(0,[z140,z1,z2,z281,z3,z5,z9]),(0,[z1,z2,z500,z3,z4,z5,z9]),(0,[z1,z2,z3,z116,z4,z5,z6]),(0,[z1,z2,z501,z3,z4,z5,z9]),(1,[z1,z3,z4,z5,z502,z11]),(0,[z1,z2,z3,z4,z5,z503,z9]),(0,[z1,z2,z504,z3,z4,z5,z9]),(0,[z1,z2,z505,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z5,z506,z9]),(0,[z507,z1,z2,z3,z4,z5,z9]),(0,[z1,z218,z98,z3,z4,z5,z9]),(0,[z1,z3,z4,z5,z9,z502,z11]),(0,[z1,z2,z3,z142,z5,z109,z9])],[(0,[z1,z462,z2,z3,z4,z5,z9]),(1,[z1,z81,z3,z42,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z508]),(0,[z1,z2,z509,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z510,z5,z9]),(0,[z1,z2,z78,z3,z4,z5,z9]),(0,[z1,z2,z511,z3,z4,z5,z9])],[(0,[z1,z2,z95,z3,z4,z5,z9]),(0,[z1,z2,z496,z3,z4,z5,z9]),(0,[z1,z512,z2,z3,z4,z5,z9]),(0,[z1,z513,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z29,z4,z5,z244]),(0,[z1,z2,z45,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z514])],[(0,[z1,z75,z3,z4,z42,z5,z9]),(0,[z1,z2,z3,z515,z4,z5,z9]),(0,[z1,z2,z516,z3,z4,z5,z9]),(0,[z1,z2,z199,z3,z4,z5,z200]),(0,[z1,z2,z3,z4,z5,z44,z9]),(0,[z1,z2,z3,z4,z517,z5,z9]),(0,[z1,z2,z3,z4,z388,z5,z11]),(0,[z518,z1,z2,z3,z4,z5,z9])],[(0,[z221,z1,z2,z105,z3,z4,z5]),(0,[z1,z2,z73,z3,z4,z5,z9]),(0,[z1,z73,z3,z136,z4,z5,z9]),(1,[z1,z2,z4,z338,z5,z9])],[(0,[z1,z2,z3,z152,z4,z5,z9]),(0,[z39,z1,z2,z3,z4,z5,z11]),(0,[z1,z3,z4,z5,z24,z9,z63]),(0,[z1,z2,z78,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z519]),(0,[z1,z2,z3,z4,z5,z520,z9])],[(1,[z1,z2,z160,z4,z5,z9]),(0,[z1,z2,z45,z3,z4,z5,z6]),(0,[z1,z2,z3,z521,z4,z5,z9])]],
   [[(0,[z1,z376,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z522,z5,z9]),(0,[z1,z2,z523,z3,z4,z5,z9]),(0,[z1,z2,z249,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z89,z9])],[(0,[z185,z1,z2,z3,z4,z5,z9]),(0,[z1,z72,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z524,z9]),(0,[z1,z3,z29,z4,z42,z5,z9]),(0,[z1,z2,z3,z4,z42,z5,z11]),(0,[z1,z2,z3,z29,z4,z5,z11]),(0,[z1,z2,z27,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z502,z11]),(0,[z1,z2,z3,z4,z9,z167,z11]),(0,[z1,z2,z525,z3,z4,z5,z9])],[(1,[z1,z2,z3,z4,z134,z9]),(0,[z57,z1,z2,z3,z4,z5,z11]),(0,[z1,z41,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z526,z4,z5,z9]),(0,[z1,z2,z527,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z528,z5,z9]),(0,[z1,z2,z105,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z529])],[(0,[z1,z2,z3,z530,z4,z5,z9]),(0,[z7,z1,z2,z3,z4,z5,z11]),(0,[z138,z2,z3,z4,z21,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z531]),(1,[z1,z3,z4,z5,z9,z502])],[(0,[z1,z26,z3,z4,z5,z10,z9]),(0,[z140,z1,z2,z3,z116,z5,z9]),(0,[z1,z2,z348,z3,z4,z5,z9]),(0,[z1,z2,z249,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z89,z6])],[(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z532,z3,z4,z5,z9]),(1,[z1,z2,z496,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z210,z11]),(0,[z1,z2,z533,z3,z4,z5,z9]),(0,[z1,z2,z27,z3,z4,z5,z6]),(0,[z1,z2,z3,z534,z4,z5,z9])],[(0,[z1,z2,z3,z4,z142,z21,z9]),(0,[z535,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z528,z5,z6]),(0,[z1,z2,z105,z3,z4,z5,z6]),(0,[z1,z2,z281,z3,z4,z109,z9])],[(0,[z1,z2,z3,z536,z4,z5,z9]),(0,[z1,z2,z17,z3,z4,z133,z9]),(0,[z1,z2,z3,z4,z5,z6,z226]),(0,[z1,z2,z3,z537,z4,z5,z9])]],
   [[(0,[z1,z538,z2,z3,z4,z5,z9]),(0,[z1,z2,z539,z3,z4,z5,z9]),(0,[z540,z1,z2,z3,z4,z5,z9]),(0,[z541,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z86]),(0,[z1,z2,z3,z4,z542,z5,z9])],[(0,[z1,z2,z3,z543,z4,z5,z9]),(1,[z1,z2,z3,z117,z5,z9]),(0,[z1,z2,z3,z4,z544,z5,z9]),(0,[z1,z2,z545,z3,z4,z5,z9]),(0,[z1,z419,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z268,z4,z109,z9])],[(0,[z1,z2,z3,z4,z338,z5,z9]),(0,[z1,z2,z3,z4,z5,z546,z9]),(0,[z1,z2,z27,z4,z30,z5,z9])],[(0,[z106,z1,z26,z3,z4,z5,z9]),(0,[z2,z3,z4,z21,z5,z62,z9]),(0,[z1,z2,z547,z3,z4,z5,z9]),(0,[z1,z2,z27,z3,z4,z5,z548]),(0,[z1,z2,z3,z4,z5,z9,z549])],[(0,[z1,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z550,z3,z4,z5,z9]),(0,[z1,z551,z2,z3,z4,z5,z9]),(0,[z1,z2,z17,z3,z4,z145,z9]),(0,[z1,z2,z552,z3,z4,z5,z9])],[(0,[z1,z2,z3,z553,z4,z5,z9]),(0,[z1,z2,z554,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z502])],[(0,[z1,z2,z3,z555,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z556,z9]),(0,[z1,z557,z2,z3,z4,z5,z9]),(0,[z1,z558,z2,z3,z4,z5,z9]),(0,[z1,z2,z559,z3,z4,z5,z9])]],
   [[(0,[z26,z2,z75,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z327,z9]),(0,[z1,z2,z3,z4,z5,z560,z9]),(0,[z1,z2,z67,z3,z4,z10,z9]),(0,[z1,z2,z3,z4,z5,z561,z9]),(0,[z1,z66,z3,z4,z5,z9,z63]),(0,[z1,z2,z562,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z563,z5,z9]),(0,[z1,z2,z3,z4,z564,z5,z9])],[(0,[z565,z1,z2,z3,z4,z5,z9]),(0,[z57,z26,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z566,z5,z9]),(0,[z1,z2,z3,z4,z5,z62,z11]),(0,[z1,z2,z3,z4,z5,z9,z567]),(1,[z1,z2,z27,z30,z5,z9])],[(1,[z1,z2,z3,z4,z171,z9]),(0,[z1,z2,z568,z3,z4,z5,z9]),(0,[z1,z2,z3,z569,z4,z5,z9]),(0,[z1,z2,z179,z67,z3,z4,z9]),(0,[z1,z2,z3,z570,z4,z5,z9])],[(0,[z185,z1,z2,z3,z4,z5,z303]),(0,[z1,z2,z3,z4,z5,z571,z9]),(0,[z1,z2,z3,z4,z144,z21,z9]),(0,[z1,z2,z3,z572,z4,z5,z9]),(0,[z39,z1,z2,z3,z4,z5,z313]),(0,[z1,z573,z2,z3,z4,z5,z9]),(0,[z1,z2,z574,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z575,z5,z9]),(0,[z1,z2,z67,z3,z4,z144,z9]),(0,[z1,z2,z3,z4,z5,z576,z9])],[(1,[z185,z2,z107,z4,z5,z9]),(0,[z1,z218,z2,z3,z4,z10,z9]),(0,[z577,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z562,z3,z4,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z9])],[(0,[z1,z579,z2,z3,z4,z5,z9])],[(0,[z1,z2,z580,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z581,z5,z9]),(0,[z1,z2,z3,z268,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z6,z452])],[(0,[z1,z2,z3,z4,z277,z5,z62]),(0,[z1,z2,z3,z4,z5,z582,z9]),(0,[z1,z218,z2,z3,z4,z144,z9]),(0,[z1,z2,z3,z4,z142,z5,z11]),(0,[z1,z2,z3,z4,z5,z9,z583])]],
   [[(0,[z1,z2,z3,z584,z4,z5,z9]),(0,[z1,z2,z3,z4,z585,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z586]),(0,[z34,z2,z3,z4,z5,z9,z210]),(0,[z1,z2,z3,z4,z5,z9,z587]),(0,[z1,z2,z3,z4,z5,z588,z9]),(0,[z1,z2,z3,z4,z5,z9,z589]),(0,[z1,z2,z3,z4,z5,z590,z9]),(0,[z1,z591,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z340,z5,z9]),(0,[z1,z2,z3,z4,z592,z5,z9]),(0,[z1,z41,z2,z3,z4,z186,z9]),(0,[z1,z2,z3,z4,z593,z5,z9])],[(0,[z0,z2,z199,z3,z4,z5,z9]),(0,[z39,z1,z72,z3,z4,z5,z9])],[(0,[z1,z2,z249,z107,z4,z5,z9]),(0,[z140,z1,z462,z3,z4,z5,z9]),(0,[z594,z1,z2,z3,z4,z5,z9])],[(0,[z185,z1,z2,z107,z4,z5,z9]),(0,[z221,z1,z66,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z595,z5,z9]),(0,[z1,z2,z3,z596,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z10,z9])],[(0,[z1,z597,z2,z3,z4,z5,z9]),(0,[z1,z2,z199,z3,z4,z5,z237]),(0,[z598,z1,z2,z3,z4,z5,z9])],[(0,[z599,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z277,z5,z9]),(0,[z600,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z601,z9]),(0,[z602,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z548,z9]),(0,[z1,z2,z3,z4,z5,z113,z11]),(0,[z1,z2,z3,z4,z5,z11,z11]),(0,[z1,z2,z249,z4,z5,z6,z9])],[(0,[z1,z2,z3,z4,z603,z5,z9]),(0,[z221,z1,z2,z3,z130,z4,z5]),(0,[z1,z41,z3,z29,z4,z5,z9])]],
   [[(0,[z604,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z10,z6]),(0,[z1,z2,z605,z3,z4,z5,z9]),(0,[z1,z606,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z607,z5,z9]),(0,[z1,z2,z3,z4,z608,z5,z9]),(0,[z1,z609,z2,z3,z4,z5,z9]),(1,[z1,z2,z67,z3,z4,z48])],[(0,[z1,z2,z3,z610,z4,z5,z9]),(0,[z611,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z612]),(0,[z1,z2,z3,z4,z5,z9,z613])],[(0,[z1,z2,z3,z4,z5,z38,z9]),(0,[z1,z2,z3,z4,z5,z614,z9]),(1,[z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z615,z5,z9]),(0,[z1,z2,z616,z3,z4,z5,z9])],[(0,[z1,z2,z2,z3,z4,z5,z9]),(0,[z106,z1,z2,z3,z4,z134,z9]),(0,[z1,z2,z3,z4,z5,z617,z9]),(1,[z1,z2,z3,z4,z5,z548]),(0,[z1,z2,z618,z3,z4,z5,z9])],[(0,[z1,z2,z619,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z620,z5,z9]),(0,[z1,z2,z3,z4,z5,z170,z9]),(0,[z1,z2,z3,z4,z5,z621,z9]),(0,[z1,z2,z3,z4,z5,z9,z622]),(0,[z1,z2,z3,z4,z623,z5,z9]),(0,[z1,z624,z2,z3,z4,z5,z9])],[(0,[z34,z1,z2,z67,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z163,z9]),(0,[z1,z625,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z397,z4,z5,z9])]],
   [[(0,[z1,z626,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z356,z9]),(0,[z1,z2,z3,z4,z5,z627,z9])],[(0,[z1,z2,z3,z4,z5,z9,z628])],[(0,[z1,z2,z75,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z629,z9]),(0,[z1,z2,z3,z630,z4,z5,z9]),(0,[z1,z2,z631,z3,z4,z5,z9])],[(0,[z0,z185,z2,z3,z4,z5,z9]),(0,[z221,z1,z2,z3,z4,z5,z11]),(0,[z632,z1,z2,z3,z4,z5,z9])],[(1,[z1,z2,z3,z4,z5,z303]),(0,[z1,z2,z633,z3,z4,z5,z9]),(0,[z1,z634,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z635,z4,z5,z9]),(0,[z1,z2,z78,z199,z4,z5,z9]),(0,[z2,z3,z116,z4,z96,z5,z9]),(0,[z1,z2,z3,z4,z62,z10,z9]),(0,[z1,z3,z4,z144,z5,z10,z9]),(0,[z1,z54,z2,z67,z3,z4,z5]),(1,[z1,z2,z179,z4,z113,z9]),(0,[z1,z2,z3,z4,z636,z5,z9]),(0,[z1,z2,z637,z3,z4,z5,z9])],[(0,[z1,z638,z2,z3,z4,z5,z9]),(0,[z1,z639,z2,z3,z4,z5,z9]),(0,[z1,z2,z78,z3,z4,z5,z11])],[(0,[z1,z2,z3,z4,z5,z9,z640]),(0,[z1,z2,z3,z4,z641,z5,z9]),(0,[z1,z2,z179,z3,z4,z133,z9]),(0,[z1,z2,z45,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z642,z9]),(0,[z643,z1,z2,z3,z4,z5,z9])]],
   [[(0,[z221,z1,z2,z3,z4,z5,z38]),(0,[z1,z2,z3,z102,z4,z5,z9]),(0,[z1,z2,z3,z4,z644,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z438]),(0,[z1,z634,z2,z3,z4,z5,z6]),(0,[z645,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z73,z3,z4,z5,z11]),(0,[z1,z2,z4,z5,z6,z9,z11]),(0,[z1,z646,z2,z3,z4,z5,z9]),(0,[z1,z647,z2,z3,z4,z5,z9])],[(0,[z140,z1,z2,z3,z4,z356,z9]),(0,[z138,z1,z2,z281,z3,z4,z9]),(0,[z1,z2,z3,z29,z4,z5,z202]),(0,[z1,z2,z3,z4,z648,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z241]),(0,[z649,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z249,z199,z4,z5,z9]),(0,[z1,z2,z650,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z394,z5,z9]),(0,[z1,z2,z179,z4,z5,z113,z9]),(0,[z1,z2,z3,z4,z5,z109,z9]),(0,[z651,z1,z2,z3,z4,z5,z9])],[(0,[z0,z57,z2,z3,z4,z5,z9]),(0,[z185,z1,z2,z199,z4,z5,z9]),(0,[z1,z2,z3,z4,z652,z5,z9]),(0,[z1,z2,z3,z653,z4,z5,z9]),(0,[z1,z2,z179,z3,z4,z145,z9]),(0,[z1,z2,z249,z3,z4,z5,z11])],[(0,[z185,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z654,z4,z5,z9]),(0,[z1,z2,z3,z4,z655,z5,z9]),(0,[z1,z656,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z268,z4,z10,z9]),(0,[z1,z2,z27,z3,z4,z5,z11]),(0,[z1,z2,z105,z3,z130,z5,z9]),(0,[z1,z2,z3,z4,z47,z5,z9])],[(0,[z1,z2,z199,z4,z5,z9,z11]),(0,[z1,z54,z2,z3,z4,z298,z9]),(0,[z1,z2,z105,z3,z4,z5,z11])],[(1,[z1,z2,z3,z4,z5,z327]),(0,[z39,z1,z2,z73,z4,z5,z9]),(1,[z1,z2,z3,z4,z9,z167]),(0,[z1,z2,z3,z4,z5,z109,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z657,z9]),(0,[z1,z2,z658,z3,z4,z5,z9]),(0,[z1,z2,z3,z268,z4,z144,z9]),(0,[z1,z2,z3,z130,z4,z5,z9])],[(0,[z1,z41,z75,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z659,z5,z9]),(0,[z39,z1,z2,z3,z4,z394,z9]),(0,[z1,z2,z660,z3,z4,z5,z9]),(0,[z1,z2,z661,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z47,z5,z6])],[(0,[z1,z662,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z10,z113,z9])],[(0,[z1,z2,z3,z4,z5,z663,z9]),(0,[z1,z2,z3,z4,z664,z5,z9]),(0,[z1,z2,z665,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z666])],[(0,[z34,z1,z2,z3,z4,z47,z5]),(0,[z1,z2,z3,z4,z5,z89,z210]),(0,[z667,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z668,z5,z9]),(0,[z1,z2,z3,z4,z5,z669,z9]),(0,[z1,z2,z3,z130,z4,z5,z6]),(0,[z1,z2,z670,z3,z4,z5,z9])],[(0,[z1,z2,z3,z671,z4,z5,z9]),(0,[z1,z2,z3,z70,z42,z5,z9]),(1,[z1,z2,z3,z4,z5,z149]),(0,[z1,z2,z672,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z673,z9]),(1,[z1,z2,z3,z4,z340,z9]),(1,[z1,z2,z3,z4,z5,z347]),(0,[z1,z674,z2,z3,z4,z5,z9]),(1,[z1,z2,z150,z3,z4,z9])],[(1,[z1,z538,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z675,z5,z9]),(0,[z1,z2,z3,z4,z676,z5,z9]),(1,[z1,z2,z3,z4,z5,z157])]],
   [[(0,[z1,z677,z2,z3,z4,z5,z9]),(0,[z7,z1,z2,z281,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z6,z678])],[(0,[z166,z1,z2,z3,z4,z5,z9]),(0,[z1,z538,z2,z75,z3,z4,z5]),(0,[z1,z2,z3,z4,z679,z5,z9]),(1,[z329,z2,z3,z4,z5,z9])],[(0,[z106,z1,z75,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z680,z9]),(0,[z1,z2,z681,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z682,z9])],[(0,[z1,z2,z3,z4,z62,z109,z9]),(0,[z1,z2,z3,z4,z5,z683,z9]),(0,[z1,z54,z2,z3,z4,z5,z89])],[(0,[z684,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z685]),(0,[z686,z1,z2,z3,z4,z5,z9]),(0,[z166,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z107,z4,z5,z6]),(1,[z1,z2,z3,z364,z5,z9]),(0,[z1,z2,z687,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z155,z5,z9]),(0,[z1,z2,z3,z4,z5,z51,z9]),(0,[z1,z2,z3,z4,z688,z5,z9]),(0,[z1,z2,z3,z4,z5,z6,z12])],[(0,[z689,z1,z2,z3,z4,z5,z9]),(0,[z57,z2,z3,z107,z4,z5,z9]),(1,[z1,z2,z3,z4,z342,z9]),(0,[z1,z2,z3,z690,z4,z5,z9])]],
   [[(0,[z1,z691,z2,z3,z4,z5,z9]),(0,[z1,z2,z17,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z11,z488])],[(1,[z1,z2,z317,z4,z5,z9]),(0,[z1,z2,z3,z692,z4,z5,z9])],[(0,[z1,z218,z3,z4,z144,z5,z9]),(0,[z1,z66,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z693,z9]),(0,[z1,z2,z3,z4,z5,z9,z678]),(0,[z1,z2,z3,z4,z5,z145,z9])],[(0,[z1,z75,z3,z4,z5,z10,z9]),(0,[z1,z2,z3,z4,z694,z5,z9]),(0,[z1,z2,z3,z4,z695,z5,z9]),(0,[z696,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z697,z4,z5,z9]),(0,[z1,z2,z3,z698,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z699]),(0,[z0,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z700,z5,z9]),(0,[z1,z2,z17,z3,z4,z5,z6])],[(0,[z1,z218,z26,z3,z4,z5,z9]),(1,[z1,z37,z3,z4,z5,z9]),(0,[z140,z1,z2,z3,z96,z5,z9]),(0,[z701,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z702,z5,z9]),(1,[z1,z2,z3,z268,z142,z9])],[(0,[z1,z2,z3,z4,z21,z5,z9]),(0,[z1,z2,z703,z3,z4,z5,z9]),(0,[z1,z2,z704,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z145,z6]),(1,[z1,z2,z3,z4,z5,z173]),(0,[z1,z2,z3,z4,z5,z705,z9])],[(0,[z1,z26,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z160,z4,z5,z9]),(0,[z1,z2,z3,z706,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z589,z11]),(0,[z1,z2,z3,z4,z5,z11,z48])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z3,z4,z5,z24,z347]),(0,[z1,z2,z707,z3,z4,z5]),(0,[z1,z708,z3,z4,z5,z9])],[(0,[z1,z2,z317,z4,z340,z9]),(0,[z1,z3,z709,z4,z5,z9])],[(0,[z1,z2,z3,z710,z5,z9]),(0,[z1,z2,z3,z4,z5,z711]),(0,[z2,z3,z4,z712,z5,z9]),(0,[z1,z713,z2,z3,z4,z5]),(0,[z329,z2,z3,z4,z342,z9]),(0,[z39,z1,z136,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z714]),(0,[z1,z2,z660,z4,z5,z11]),(0,[z316,z1,z2,z150,z3,z4])],[(0,[z1,z2,z715,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z303]),(0,[z1,z2,z3,z4,z716,z9]),(0,[z1,z2,z3,z4,z5,z717]),(0,[z1,z718,z2,z3,z4,z5]),(0,[z138,z2,z3,z4,z21,z9]),(0,[z1,z122,z3,z4,z5,z6]),(0,[z1,z609,z3,z4,z10,z9])],[(0,[z1,z2,z3,z4,z719,z9]),(0,[z1,z81,z3,z42,z5,z11])],[(0,[z1,z720,z2,z3,z4,z5]),(0,[z1,z2,z3,z721,z5,z9]),(0,[z1,z722,z3,z4,z5,z9]),(0,[z1,z37,z3,z4,z340,z9]),(0,[z1,z2,z4,z5,z6,z236])],[(0,[z1,z2,z123,z4,z5,z9]),(0,[z1,z2,z199,z4,z5,z157]),(0,[z39,z1,z136,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z723]),(1,[z1,z3,z4,z5,z724])],[(0,[z1,z2,z3,z4,z5,z725]),(0,[z141,z2,z3,z306,z5,z9]),(0,[z1,z2,z543,z4,z5,z11]),(0,[z138,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z5,z726]),(0,[z1,z2,z4,z727,z338,z5]),(0,[z309,z1,z2,z150,z3,z4])]],
   [[(0,[z1,z2,z3,z4,z728,z9]),(0,[z1,z2,z729,z4,z5,z9]),(0,[z140,z2,z95,z3,z96,z5]),(0,[z1,z54,z2,z258,z4,z5]),(0,[z730,z2,z3,z4,z5,z9]),(0,[z1,z3,z4,z5,z11,z731])],[(0,[z1,z2,z249,z4,z5,z237]),(0,[z1,z2,z732,z4,z5,z9]),(0,[z2,z3,z116,z712,z5,z9]),(0,[z221,z2,z3,z4,z636,z5]),(0,[z1,z3,z733,z42,z5,z9]),(0,[z1,z2,z67,z3,z4,z682]),(0,[z1,z2,z3,z734,z5,z9]),(0,[z1,z2,z3,z4,z167,z11]),(0,[z1,z735,z3,z4,z5,z9])],[(0,[z1,z2,z736,z3,z4,z9]),(0,[z1,z2,z160,z4,z5,z11]),(0,[z1,z2,z123,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z737]),(0,[z1,z2,z348,z67,z4,z9]),(0,[z1,z3,z4,z5,z11,z738])],[(0,[z1,z739,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z740,z9]),(0,[z34,z211,z2,z3,z4,z5]),(0,[z1,z2,z553,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z741])],[(0,[z1,z2,z3,z742,z5,z9]),(0,[z1,z2,z258,z4,z47,z5]),(0,[z1,z98,z43,z3,z4,z10])],[(0,[z1,z2,z3,z4,z134,z11]),(0,[z1,z2,z3,z4,z5,z743]),(0,[z1,z2,z3,z4,z182,z9]),(0,[z1,z3,z744,z4,z5,z9])],[(0,[z2,z199,z107,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z745]),(0,[z1,z2,z4,z5,z6,z256])],[(0,[z1,z2,z746,z3,z5,z9]),(0,[z1,z3,z4,z733,z5,z9]),(0,[z1,z120,z3,z4,z10,z9]),(0,[z1,z2,z494,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z747,z5,z9]),(0,[z1,z75,z3,z4,z170,z9]),(0,[z1,z37,z317,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z748])],[(0,[z1,z2,z3,z4,z182,z6]),(0,[z1,z46,z3,z4,z5,z589])],[(0,[z1,z2,z3,z4,z5,z749]),(0,[z1,z2,z3,z4,z750,z5]),(0,[z7,z2,z3,z4,z62,z9])],[(0,[z1,z2,z751,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z200]),(0,[z1,z2,z3,z4,z5,z752]),(0,[z1,z2,z3,z5,z9,z753]),(0,[z1,z2,z3,z4,z5,z202]),(0,[z1,z754,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z755,z11]),(0,[z1,z2,z3,z4,z5,z756])],[(0,[z1,z2,z757,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z758]),(0,[z1,z2,z3,z117,z5,z11])],[(0,[z1,z2,z3,z4,z5,z759]),(0,[z1,z2,z3,z4,z340,z9]),(0,[z1,z2,z3,z4,z5,z347]),(0,[z1,z72,z73,z4,z5,z347]),(0,[z1,z2,z150,z3,z4,z9]),(0,[z1,z2,z3,z268,z142,z11]),(0,[z1,z3,z4,z9,z167,z502]),(0,[z1,z2,z3,z268,z142,z173])],[(0,[z1,z2,z3,z4,z760,z9]),(0,[z7,z2,z3,z4,z62,z6]),(0,[z1,z2,z3,z4,z5,z761]),(0,[z1,z762,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z9,z763]),(0,[z1,z2,z4,z5,z764,z11]),(0,[z138,z2,z3,z4,z765,z9]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z2,z637,z4,z5,z6]),(0,[z1,z2,z767,z4,z5,z9])]],
   [[(0,[z1,z2,z768,z4,z5,z9]),(0,[z329,z2,z3,z4,z5,z9]),(0,[z1,z2,z78,z635,z5,z9]),(0,[z1,z2,z3,z4,z5,z219]),(0,[z140,z2,z3,z152,z96,z9]),(0,[z1,z2,z3,z4,z769,z9]),(0,[z1,z41,z3,z29,z5,z9]),(0,[z1,z2,z348,z4,z5,z770]),(0,[z1,z46,z67,z3,z4,z5])],[(0,[z1,z2,z3,z4,z340,z6]),(0,[z1,z771,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z772]),(0,[z1,z114,z3,z4,z10,z9])],[(0,[z1,z2,z3,z4,z773,z9]),(0,[z1,z2,z496,z3,z364,z5])],[(0,[z1,z2,z3,z4,z5,z774]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z98,z4,z338,z10,z9]),(0,[z1,z2,z3,z4,z5,z724]),(1,[z1,z2,z4,z5,z776])],[(0,[z1,z2,z777,z3,z4,z9]),(0,[z1,z2,z778,z3,z4,z5]),(0,[z1,z2,z3,z4,z779,z5]),(0,[z329,z2,z3,z4,z5,z6]),(0,[z1,z41,z3,z29,z5,z6]),(0,[z1,z2,z27,z30,z5,z11])],[(0,[z1,z2,z3,z4,z171,z11]),(0,[z1,z2,z3,z4,z780,z9]),(0,[z1,z2,z3,z364,z5,z9]),(0,[z1,z2,z3,z4,z781,z5]),(0,[z1,z3,z4,z782,z10,z9]),(0,[z1,z2,z478,z4,z5,z11])],[(0,[z185,z2,z783,z4,z5,z9]),(0,[z1,z54,z687,z3,z4,z5]),(0,[z1,z2,z3,z4,z342,z9]),(0,[z1,z2,z784,z4,z5,z9])],[(0,[z1,z2,z3,z785,z5,z9]),(0,[z185,z2,z107,z4,z5,z11]),(0,[z1,z786,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z244]),(0,[z1,z2,z3,z4,z5,z787]),(0,[z1,z54,z3,z4,z5,z724])]],
   [[(0,[z1,z2,z317,z4,z5,z9]),(0,[z7,z122,z3,z4,z62,z9]),(0,[z1,z2,z272,z4,z5,z11]),(0,[z1,z2,z4,z5,z6,z302])],[(0,[z106,z538,z75,z3,z4,z5]),(0,[z1,z2,z788,z3,z5,z9]),(0,[z1,z2,z269,z4,z5,z6]),(0,[z1,z789,z3,z4,z5,z9])],[(0,[z1,z2,z3,z712,z5,z9]),(0,[z790,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z342,z6]),(0,[z1,z791,z2,z3,z4,z5])],[(0,[z2,z783,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z9,z792]),(0,[z1,z2,z348,z4,z145,z9]),(0,[z1,z2,z3,z4,z793,z5]),(0,[z1,z3,z4,z144,z782,z9]),(0,[z1,z2,z4,z5,z621,z11])],[(0,[z1,z2,z107,z4,z167,z11]),(0,[z1,z2,z3,z4,z794,z9]),(0,[z1,z2,z3,z4,z9,z795]),(0,[z1,z384,z3,z42,z5,z9])],[(0,[z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z796]),(0,[z1,z54,z3,z4,z298,z24]),(0,[z1,z2,z3,z4,z5,z173])],[(0,[z1,z2,z441,z4,z5,z11]),(0,[z797,z75,z3,z4,z5,z9]),(0,[z1,z2,z258,z4,z5,z9]),(0,[z140,z2,z3,z96,z5,z327]),(1,[z2,z3,z712,z5,z9]),(0,[z1,z8,z281,z3,z4,z9]),(0,[z1,z606,z3,z4,z10,z9]),(0,[z1,z2,z150,z3,z4,z167]),(0,[z1,z2,z3,z268,z142,z84])],[(0,[z1,z2,z3,z798,z4,z5]),(0,[z140,z2,z670,z3,z5,z9]),(0,[z1,z2,z105,z3,z87,z5]),(0,[z1,z2,z3,z4,z799,z9]),(0,[z1,z2,z3,z4,z800,z9])]],
   [[(0,[z1,z2,z3,z4,z801,z9]),(0,[z1,z2,z3,z802,z4,z5]),(0,[z57,z2,z107,z4,z5,z11]),(0,[z1,z2,z803,z4,z5,z9]),(0,[z2,z3,z4,z5,z765,z9]),(0,[z1,z2,z258,z4,z5,z427]),(0,[z329,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z4,z5,z804]),(0,[z1,z805,z3,z4,z5,z9]),(0,[z1,z2,z3,z142,z806,z9])],[(0,[z1,z2,z3,z117,z5,z313]),(0,[z1,z2,z3,z4,z167,z137]),(0,[z1,z2,z3,z4,z5,z776])],[(0,[z1,z2,z496,z3,z4,z10]),(0,[z1,z2,z258,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z807]),(0,[z1,z66,z2,z150,z3,z4]),(0,[z1,z2,z3,z374,z5,z89])],[(0,[z1,z2,z3,z4,z5,z808]),(0,[z809,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z810,z4,z9]),(0,[z1,z2,z3,z4,z811,z9]),(0,[z1,z98,z348,z4,z10,z9]),(0,[z316,z2,z3,z4,z5,z438])],[(0,[z1,z2,z3,z4,z5,z812]),(0,[z1,z66,z3,z4,z5,z63])],[(0,[z1,z2,z3,z4,z5,z813]),(0,[z1,z2,z3,z4,z342,z131]),(0,[z1,z2,z254,z3,z4,z339])],[(0,[z1,z2,z67,z3,z4,z683]),(0,[z329,z2,z3,z155,z5,z9]),(0,[z814,z2,z3,z4,z5,z9]),(0,[z39,z1,z136,z4,z342,z9]),(0,[z1,z3,z4,z5,z24,z131]),(0,[z1,z2,z348,z4,z5,z815]),(0,[z1,z2,z78,z70,z5,z44]),(0,[z1,z46,z3,z4,z5,z89]),(0,[z459,z2,z3,z4,z5,z226])]],
   [[(0,[z40,z2,z3,z4,z394,z9]),(0,[z1,z2,z3,z4,z5,z816]),(0,[z817,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z5,z818,z9]),(0,[z110,z2,z3,z4,z5,z427])],[(0,[z140,z2,z160,z96,z5,z9]),(0,[z1,z373,z3,z29,z5,z9]),(0,[z1,z2,z179,z415,z4,z9])],[(0,[z1,z107,z4,z5,z502,z11]),(0,[z1,z2,z819,z4,z5,z9]),(1,[z1,z3,z733,z5,z9]),(0,[z1,z2,z3,z4,z5,z820]),(0,[z1,z2,z562,z3,z5,z678])],[(0,[z57,z198,z3,z4,z5,z9]),(0,[z1,z122,z3,z4,z5,z11]),(0,[z34,z2,z505,z3,z4,z5]),(0,[z1,z3,z29,z733,z5,z9])],[(0,[z1,z2,z3,z4,z5,z821]),(0,[z1,z2,z3,z4,z47,z91]),(0,[z1,z72,z73,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z1,z2,z823,z3,z4,z170])],[(0,[z1,z824,z3,z4,z5,z9]),(0,[z1,z2,z160,z4,z356,z9]),(0,[z1,z2,z3,z4,z5,z825]),(0,[z1,z2,z3,z155,z342,z9]),(0,[z1,z2,z3,z4,z5,z826])],[(0,[z1,z2,z199,z4,z5,z303]),(0,[z827,z2,z3,z4,z5,z9]),(0,[z39,z1,z136,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z84])],[(0,[z138,z2,z3,z4,z21,z11]),(0,[z34,z1,z2,z150,z3,z4]),(0,[z1,z2,z828,z4,z5,z9]),(0,[z1,z2,z3,z4,z716,z11]),(0,[z1,z2,z150,z3,z4,z48])]],
   [[(0,[z1,z2,z829,z3,z4,z5]),(0,[z140,z2,z317,z96,z5,z9]),(0,[z221,z440,z2,z3,z4,z5]),(0,[z1,z72,z73,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z830]),(0,[z1,z2,z4,z831,z5,z9]),(0,[z1,z832,z3,z4,z5,z9]),(0,[z1,z46,z3,z4,z388,z5])],[(0,[z1,z2,z3,z833,z5,z9]),(0,[z1,z2,z95,z3,z4,z5]),(0,[z1,z2,z3,z834,z4,z5]),(0,[z1,z2,z123,z4,z5,z11]),(0,[z1,z2,z3,z4,z835,z9]),(0,[z1,z41,z3,z29,z5,z202]),(0,[z1,z836,z3,z4,z5,z9]),(0,[z1,z2,z27,z30,z5,z28]),(0,[z2,z3,z4,z5,z11,z837])],[(0,[z1,z2,z3,z4,z838,z11])],[(0,[z1,z2,z3,z4,z5,z839]),(0,[z1,z2,z199,z4,z167,z11]),(0,[z140,z37,z3,z96,z5,z9]),(0,[z1,z2,z3,z4,z340,z219]),(0,[z1,z2,z840,z3,z4,z5]),(0,[z1,z2,z841,z3,z4,z5]),(0,[z842,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z133,z486,z9]),(0,[z1,z2,z3,z5,z9,z843])],[(0,[z1,z25,z2,z3,z4,z5]),(0,[z1,z844,z3,z4,z5,z9]),(0,[z1,z2,z3,z268,z648,z9]),(0,[z1,z2,z734,z30,z5,z9])],[(0,[z1,z2,z3,z4,z5,z845]),(0,[z2,z783,z107,z4,z5,z9]),(0,[z1,z2,z846,z3,z4,z5]),(0,[z7,z2,z3,z364,z62,z9]),(0,[z1,z2,z4,z5,z9,z847]),(0,[z1,z2,z3,z4,z5,z848]),(0,[z1,z2,z3,z849,z5,z9]),(0,[z1,z2,z150,z4,z6,z11])],[(0,[z1,z639,z3,z4,z10,z9]),(0,[z1,z2,z783,z4,z5,z9]),(0,[z349,z2,z107,z4,z5,z9]),(0,[z1,z2,z3,z4,z850,z5]),(0,[z1,z2,z823,z3,z4,z5]),(0,[z1,z2,z3,z4,z59,z145]),(0,[z1,z419,z3,z4,z5,z502])]],
   [[(0,[z1,z797,z3,z4,z5,z9]),(0,[z1,z2,z107,z4,z5,z11]),(0,[z1,z493,z3,z4,z10,z9]),(0,[z2,z3,z4,z5,z851,z210]),(0,[z221,z1,z46,z3,z4,z5]),(0,[z1,z2,z4,z5,z852,z9]),(0,[z1,z2,z3,z4,z5,z853])],[(0,[z0,z2,z199,z4,z5,z9]),(0,[z1,z2,z4,z5,z6,z385]),(0,[z1,z2,z854,z3,z4,z5]),(0,[z1,z2,z67,z3,z4,z59]),(0,[z1,z2,z3,z4,z182,z11]),(0,[z1,z3,z744,z4,z5,z11])],[(0,[z34,z2,z3,z4,z5,z226]),(0,[z1,z2,z3,z4,z855,z9]),(1,[z1,z3,z4,z782,z9])],[(0,[z1,z2,z4,z856,z5,z9]),(1,[z2,z783,z4,z5,z9]),(0,[z1,z2,z550,z4,z5,z11]),(0,[z1,z2,z4,z133,z342,z9]),(0,[z1,z2,z3,z4,z857,z170]),(0,[z1,z2,z3,z858,z4,z5]),(0,[z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z4,z5,z6,z11]),(0,[z1,z634,z3,z4,z5,z300]),(0,[z1,z2,z3,z4,z859,z9])],[(1,[z797,z3,z4,z5,z9]),(0,[z1,z2,z4,z5,z237,z11]),(0,[z1,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z4,z763,z11])],[(0,[z1,z2,z3,z4,z5,z860]),(0,[z0,z2,z199,z4,z5,z6]),(0,[z1,z2,z3,z4,z861,z9]),(0,[z1,z81,z3,z733,z5,z9]),(0,[z1,z2,z3,z4,z5,z137]),(0,[z1,z2,z3,z4,z5,z862])],[(0,[z140,z2,z174,z3,z96,z9]),(0,[z7,z2,z3,z4,z62,z11]),(0,[z1,z2,z3,z4,z5,z863]),(0,[z1,z41,z3,z29,z5,z244]),(0,[z1,z2,z3,z4,z5,z864])],[(0,[z1,z2,z3,z4,z865,z9]),(0,[z1,z2,z866,z4,z5,z9]),(0,[z1,z2,z867,z4,z5,z9]),(0,[z1,z2,z317,z4,z5,z219]),(0,[z1,z2,z3,z142,z356,z9]),(0,[z443,z2,z3,z4,z62,z9]),(0,[z2,z3,z4,z5,z851,z9]),(0,[z1,z3,z4,z5,z868,z11]),(0,[z1,z2,z4,z5,z6,z776])]],
   [[(0,[z106,z25,z75,z3,z4,z5]),(0,[z649,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z4,z869,z9]),(0,[z1,z2,z3,z870,z5,z9]),(0,[z1,z2,z45,z150,z4,z11]),(0,[z871,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z872,z5,z9]),(0,[z1,z2,z3,z4,z5,z873]),(0,[z1,z2,z3,z4,z340,z11]),(0,[z1,z2,z3,z4,z874,z9]),(0,[z1,z2,z3,z4,z875,z5]),(0,[z1,z3,z4,z5,z24,z724]),(0,[z1,z2,z150,z3,z4,z11]),(0,[z1,z46,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z876,z9]),(0,[z1,z2,z3,z152,z4,z9]),(0,[z1,z762,z3,z4,z5,z11])],[(0,[z1,z37,z3,z4,z5,z219]),(0,[z1,z2,z3,z155,z5,z9]),(0,[z1,z2,z3,z4,z877,z9]),(0,[z1,z2,z3,z4,z5,z878]),(0,[z1,z2,z3,z4,z5,z879]),(0,[z1,z880,z2,z3,z4,z5]),(0,[z1,z2,z3,z268,z806,z9])],[(0,[z1,z3,z4,z5,z881,z9]),(0,[z454,z2,z199,z4,z5,z9]),(0,[z140,z2,z3,z96,z5,z9]),(0,[z329,z2,z3,z4,z5,z11]),(0,[z1,z41,z3,z29,z5,z11]),(0,[z1,z2,z4,z5,z9,z882]),(0,[z1,z54,z3,z4,z5,z24]),(0,[z1,z46,z3,z4,z5,z6])],[(0,[z40,z2,z3,z4,z5,z313]),(0,[z883,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z170,z9]),(0,[z2,z3,z4,z5,z9,z884])],[(0,[z1,z2,z3,z152,z4,z6]),(0,[z1,z2,z105,z258,z4,z5]),(0,[z1,z72,z709,z4,z5,z9]),(0,[z1,z2,z3,z4,z857,z5]),(0,[z1,z2,z3,z4,z885,z5])],[(0,[z1,z2,z3,z4,z5,z886]),(0,[z1,z2,z3,z155,z5,z6]),(0,[z1,z2,z3,z117,z394,z9])]],
   [[(0,[z1,z887,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z888,z9]),(0,[z1,z2,z3,z4,z356,z9]),(0,[z140,z2,z3,z96,z5,z6]),(0,[z1,z2,z889,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z890])],[(0,[z1,z2,z3,z4,z891,z5]),(0,[z1,z2,z3,z364,z5,z11]),(0,[z541,z2,z3,z4,z21,z9]),(0,[z1,z73,z709,z4,z5,z9]),(0,[z1,z2,z3,z4,z170,z6]),(0,[z1,z2,z3,z892,z4,z5]),(0,[z1,z2,z4,z5,z9,z776]),(0,[z1,z2,z3,z5,z806,z9])],[(0,[z1,z2,z3,z4,z893,z9]),(0,[z1,z2,z894,z3,z4,z5]),(0,[z1,z2,z3,z4,z342,z11]),(0,[z1,z2,z3,z4,z5,z895])],[(0,[z1,z2,z3,z4,z5,z896]),(0,[z1,z2,z3,z4,z897,z9]),(0,[z1,z898,z3,z4,z5,z9]),(0,[z1,z2,z899,z4,z5,z9]),(0,[z1,z2,z3,z4,z900,z9]),(0,[z1,z2,z3,z4,z5,z843])],[(0,[z106,z797,z3,z4,z5,z9]),(0,[z361,z2,z199,z4,z5,z9]),(0,[z1,z2,z317,z4,z5,z11]),(0,[z1,z2,z3,z4,z356,z6]),(0,[z901,z2,z3,z4,z5,z9])],[(0,[z1,z2,z55,z4,z5,z11]),(0,[z39,z1,z136,z4,z5,z131])],[(0,[z1,z462,z3,z4,z5,z327]),(0,[z1,z2,z902,z4,z5,z9]),(0,[z34,z1,z2,z3,z4,z182]),(0,[z1,z2,z619,z3,z5,z12]),(0,[z1,z426,z3,z4,z144,z9])],[(0,[z1,z2,z61,z3,z5,z9]),(0,[z1,z2,z3,z4,z903,z9]),(0,[z2,z904,z3,z4,z5,z9]),(0,[z1,z2,z45,z4,z167,z11])]],
   [[(0,[z1,z2,z199,z4,z5,z11]),(0,[z1,z37,z3,z4,z5,z11]),(0,[z2,z3,z4,z765,z62,z9])],[(0,[z1,z2,z3,z4,z5,z905])],[(0,[z1,z2,z150,z199,z4,z11]),(0,[z1,z2,z3,z142,z663,z9]),(0,[z1,z2,z3,z4,z9,z906])],[(0,[z1,z2,z3,z4,z907,z9]),(0,[z1,z2,z290,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z908]),(0,[z1,z2,z61,z3,z5,z6]),(0,[z1,z2,z3,z155,z5,z131]),(0,[z1,z46,z2,z150,z3,z4]),(0,[z1,z2,z3,z4,z799,z11])],[(0,[z1,z2,z3,z909,z5,z9]),(0,[z0,z2,z783,z4,z5,z9]),(0,[z1,z2,z3,z910,z5,z9]),(0,[z39,z1,z136,z155,z5,z9]),(0,[z1,z2,z3,z4,z5,z911]),(0,[z1,z2,z912,z4,z5,z9])],[(0,[z1,z2,z415,z4,z5,z6])],[(0,[z2,z75,z107,z4,z5,z11]),(0,[z1,z2,z299,z4,z5,z11]),(0,[z1,z2,z3,z4,z913,z9]),(0,[z1,z46,z3,z4,z5,z63])],[(0,[z1,z2,z3,z4,z5,z914]),(0,[z1,z2,z915,z3,z4,z9]),(0,[z1,z45,z4,z5,z502,z11]),(0,[z1,z2,z3,z806,z109,z9])]],
   [[(0,[z1,z2,z3,z4,z811,z11])],[(0,[z1,z2,z916,z3,z4,z5]),(0,[z1,z462,z160,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z917]),(0,[z1,z2,z3,z4,z9,z918]),(0,[z1,z2,z348,z4,z133,z9]),(0,[z1,z2,z348,z4,z59,z5]),(0,[z1,z2,z3,z74,z5,z89]),(0,[z919,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z920,z9])],[(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z3,z4,z5,z922]),(0,[z1,z2,z258,z4,z5,z210]),(0,[z1,z2,z3,z49,z5,z89]),(0,[z1,z923,z2,z3,z4,z5])],[(0,[z0,z2,z199,z4,z5,z200]),(0,[z1,z2,z281,z3,z154,z9]),(1,[z1,z709,z4,z5,z9]),(0,[z1,z2,z924,z3,z4,z5]),(0,[z1,z2,z3,z4,z925,z9])],[(0,[z135,z1,z2,z281,z3,z9]),(0,[z1,z2,z3,z4,z926,z5]),(0,[z1,z2,z3,z927,z5,z9]),(0,[z1,z2,z105,z3,z5,z843])],[(0,[z57,z26,z3,z4,z5,z9]),(0,[z1,z41,z3,z515,z5,z9]),(0,[z1,z2,z3,z928,z5,z9]),(0,[z1,z2,z281,z3,z425,z9]),(0,[z1,z46,z3,z4,z9,z167]),(0,[z1,z2,z672,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z929]),(0,[z1,z2,z3,z4,z5,z851]),(0,[z1,z930,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z931]),(0,[z1,z2,z3,z4,z5,z932]),(0,[z933,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z770]),(0,[z1,z2,z207,z3,z5,z241]),(0,[z1,z2,z3,z374,z5,z118])]],
   [[(0,[z2,z107,z4,z5,z438,z11]),(0,[z1,z72,z73,z4,z5,z11]),(0,[z1,z2,z3,z4,z934,z9]),(0,[z1,z54,z3,z4,z182,z24]),(0,[z1,z2,z3,z248,z5,z89])],[(0,[z57,z26,z3,z4,z5,z6]),(0,[z185,z2,z107,z4,z5,z197]),(0,[z1,z66,z539,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z163]),(0,[z1,z307,z3,z4,z144,z9]),(0,[z1,z2,z78,z70,z5,z11]),(0,[z1,z376,z3,z4,z5,z452])],[(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z2,z3,z936,z4,z5]),(1,[z2,z3,z4,z5,z851]),(0,[z1,z66,z3,z4,z5,z131])],[(0,[z57,z797,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z937]),(0,[z309,z2,z107,z4,z5,z9]),(0,[z1,z2,z3,z4,z765,z9]),(0,[z1,z2,z3,z938,z4,z5])],[(0,[z1,z2,z53,z4,z5,z11]),(0,[z1,z2,z4,z5,z335,z11]),(0,[z1,z2,z3,z4,z5,z939]),(0,[z1,z46,z150,z3,z4,z9])],[(0,[z106,z75,z3,z4,z134,z9]),(0,[z1,z2,z3,z4,z5,z940]),(0,[z1,z2,z3,z4,z356,z327]),(0,[z1,z66,z2,z258,z4,z5]),(0,[z40,z2,z3,z117,z5,z9]),(0,[z1,z2,z3,z4,z5,z941]),(0,[z1,z2,z176,z4,z5,z6])],[(0,[z1,z2,z942,z3,z4,z5])],[(0,[z1,z2,z3,z4,z943,z9]),(0,[z1,z2,z944,z3,z4,z5]),(0,[z1,z2,z3,z4,z945,z9]),(0,[z1,z2,z3,z4,z5,z197]),(1,[z2,z3,z4,z765,z9]),(0,[z1,z2,z3,z946,z5,z9]),(0,[z1,z557,z3,z4,z144,z9]),(0,[z1,z2,z3,z4,z5,z947])]],
   [[(0,[z140,z2,z3,z96,z340,z9]),(0,[z1,z948,z8,z3,z4,z5]),(0,[z1,z2,z3,z4,z277,z5]),(0,[z1,z2,z61,z3,z142,z9]),(0,[z362,z2,z3,z4,z21,z9]),(0,[z1,z54,z3,z4,z5,z502]),(0,[z1,z2,z523,z4,z5,z11]),(0,[z316,z1,z46,z3,z4,z5]),(0,[z1,z2,z949,z3,z4,z5])],[(0,[z1,z2,z950,z4,z5,z9]),(0,[z138,z2,z3,z235,z4,z9]),(0,[z1,z46,z3,z4,z47,z5])],[(0,[z1,z8,z3,z4,z5,z9]),(0,[z140,z2,z3,z397,z96,z5]),(0,[z1,z2,z162,z4,z5,z6]),(0,[z1,z2,z150,z3,z4,z241]),(0,[z1,z2,z67,z3,z4,z756])],[(0,[z1,z951,z3,z4,z5,z9]),(0,[z140,z2,z3,z96,z5,z219]),(0,[z1,z2,z272,z30,z5,z9]),(0,[z1,z2,z3,z4,z59,z298]),(0,[z1,z2,z67,z3,z4,z149]),(0,[z1,z2,z45,z4,z5,z11])],[(0,[z1,z2,z3,z4,z952,z9]),(0,[z1,z41,z3,z29,z170,z9]),(0,[z1,z150,z3,z4,z502,z11]),(0,[z1,z2,z3,z4,z806,z9])],[(0,[z1,z26,z3,z4,z171,z9]),(0,[z1,z2,z3,z953,z5,z9]),(0,[z0,z2,z199,z4,z5,z11]),(0,[z1,z2,z3,z954,z5,z9]),(0,[z138,z1,z2,z61,z3,z9]),(0,[z1,z3,z4,z955,z5,z9]),(0,[z309,z1,z46,z3,z4,z5])],[(0,[z1,z2,z3,z4,z956,z9]),(0,[z1,z8,z3,z4,z5,z6]),(0,[z957,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z237]),(0,[z1,z2,z3,z4,z356,z219]),(0,[z39,z40,z136,z4,z5,z9]),(0,[z1,z2,z45,z4,z5,z776])]],
   [[(0,[z1,z2,z174,z3,z4,z9]),(0,[z7,z2,z3,z4,z765,z9]),(0,[z1,z98,z3,z4,z59,z10]),(0,[z1,z2,z4,z59,z338,z5]),(0,[z1,z2,z3,z4,z10,z173])],[(0,[z1,z2,z3,z4,z5,z958]),(0,[z1,z2,z3,z959,z5,z9]),(0,[z1,z2,z27,z734,z5,z9]),(0,[z1,z2,z78,z734,z5,z9])],[(0,[z1,z2,z95,z3,z152,z4]),(0,[z1,z2,z3,z4,z5,z960]),(0,[z1,z54,z3,z4,z5,z583])],[(0,[z1,z2,z961,z3,z5,z9]),(0,[z1,z2,z3,z4,z5,z962]),(0,[z1,z2,z3,z4,z5,z963]),(0,[z1,z3,z4,z5,z502,z347]),(0,[z1,z98,z3,z4,z10,z9]),(0,[z1,z2,z3,z4,z144,z173]),(0,[z1,z2,z184,z4,z5,z11])],[(0,[z1,z462,z3,z4,z5,z9]),(0,[z1,z2,z174,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z964])],[(0,[z106,z75,z3,z4,z171,z9]),(0,[z1,z2,z3,z4,z965,z9]),(0,[z140,z2,z3,z712,z5,z9]),(0,[z2,z3,z4,z5,z38,z851]),(0,[z1,z2,z3,z4,z5,z313]),(0,[z1,z218,z3,z4,z144,z9]),(0,[z1,z2,z105,z3,z5,z12])],[(0,[z1,z966,z3,z4,z5,z9]),(0,[z1,z2,z3,z152,z4,z11]),(0,[z967,z2,z3,z4,z5,z9]),(0,[z1,z66,z3,z4,z5,z347]),(0,[z1,z2,z3,z4,z5,z968]),(0,[z1,z2,z3,z4,z5,z815])],[(0,[z1,z2,z969,z4,z5,z9]),(0,[z1,z2,z970,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z2,z317,z4,z356,z9]),(0,[z1,z2,z3,z155,z5,z11]),(0,[z1,z2,z3,z4,z5,z972]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z98,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z5,z974])]],
   [[(0,[z1,z2,z975,z4,z5,z9]),(0,[z1,z2,z3,z976,z4,z5]),(0,[z1,z2,z977,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z978]),(0,[z1,z462,z3,z4,z5,z6]),(0,[z140,z2,z3,z96,z5,z11]),(0,[z141,z2,z3,z712,z5,z9]),(0,[z1,z979,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z2,z3,z4,z5,z981]),(1,[z1,z2,z4,z818,z9]),(0,[z1,z2,z179,z4,z818,z9]),(0,[z1,z150,z3,z4,z9,z502])],[(0,[z1,z982,z2,z3,z4,z5]),(0,[z1,z2,z160,z4,z5,z983]),(0,[z1,z2,z3,z4,z984,z9]),(0,[z1,z2,z3,z4,z170,z11])],[(0,[z1,z46,z3,z4,z5,z238])],[(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z2,z3,z4,z986,z9]),(0,[z0,z2,z103,z4,z5,z9]),(0,[z26,z797,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z37,z3,z4,z356,z9]),(0,[z1,z2,z4,z5,z226,z11])],[(0,[z141,z2,z3,z116,z5,z6]),(0,[z39,z1,z383,z4,z5,z9]),(0,[z1,z66,z3,z4,z5,z724]),(0,[z1,z2,z67,z3,z4,z298]),(0,[z1,z988,z3,z4,z5,z9]),(0,[z1,z2,z889,z3,z4,z11]),(0,[z1,z2,z3,z4,z5,z989])],[(0,[z1,z990,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z1,z2,z3,z4,z5,z992]),(0,[z1,z2,z3,z4,z5,z993])],[(0,[z1,z2,z994,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z995]),(0,[z1,z8,z3,z4,z62,z9]),(0,[z1,z2,z3,z130,z5,z843])],[(0,[z1,z2,z3,z268,z608,z9]),(0,[z329,z2,z3,z4,z394,z9]),(0,[z1,z2,z43,z3,z4,z5]),(0,[z1,z2,z249,z4,z5,z6])]],
   [[(0,[z1,z2,z228,z4,z5,z11]),(0,[z1,z996,z3,z4,z5,z9])],[(0,[z1,z597,z3,z4,z10,z9]),(0,[z1,z2,z3,z4,z5,z764]),(0,[z1,z2,z3,z997,z5,z9]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z2,z3,z4,z5,z999,z9]),(0,[z1,z2,z3,z4,z5,z1000])],[(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z2,z460,z30,z5,z9]),(0,[z1,z1002,z2,z3,z4,z5]),(0,[z1,z2,z3,z733,z5,z9])],[(0,[z216,z75,z3,z4,z5,z9]),(0,[z1,z2,z1003,z3,z4,z5]),(0,[z7,z2,z3,z4,z277,z62]),(0,[z1004,z2,z3,z4,z5,z9]),(0,[z1,z46,z3,z4,z5,z9]),(0,[z1,z2,z4,z734,z5,z9]),(0,[z1,z3,z4,z5,z502,z11]),(0,[z1,z2,z150,z3,z4,z86])],[(0,[z1,z2,z3,z4,z1005,z9]),(0,[z1,z2,z123,z4,z5,z237]),(0,[z309,z2,z3,z4,z5,z210]),(1,[z1,z2,z3,z4,z756])],[(0,[z1,z1006,z3,z4,z5,z9]),(0,[z1,z2,z1007,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z3,z4,z5,z6,z502])],[(0,[z1,z2,z3,z4,z5,z1009]),(0,[z39,z1,z136,z4,z5,z313])],[(0,[z221,z1,z2,z150,z3,z4]),(0,[z1,z72,z4,z165,z5,z9]),(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z2,z3,z4,z5,z1011])]],
   [[(0,[z1,z2,z1012,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z2,z3,z1014,z4,z9]),(0,[z221,z2,z3,z4,z5,z851])],[(0,[z1,z2,z421,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z3,z1016,z5,z9]),(0,[z1,z2,z3,z4,z5,z1017]),(0,[z1,z2,z3,z33,z142,z9]),(0,[z1,z2,z258,z130,z4,z5]),(0,[z34,z2,z504,z3,z4,z5]),(0,[z1,z2,z4,z338,z5,z9]),(0,[z1,z2,z383,z4,z5,z6]),(0,[z1,z66,z151,z3,z4,z5])],[(0,[z1,z2,z67,z258,z4,z5]),(0,[z1,z66,z3,z4,z5,z502]),(0,[z1,z66,z3,z4,z5,z705]),(0,[z1,z2,z3,z4,z1018,z5]),(0,[z1,z2,z3,z4,z5,z1019])],[(0,[z1,z2,z3,z4,z1020,z9]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z2,z1022,z3,z4,z5]),(0,[z1,z2,z915,z3,z4,z11])],[(0,[z1,z2,z3,z4,z5,z1023]),(0,[z1,z2,z3,z4,z186,z9]),(0,[z1,z2,z3,z4,z145,z756])],[(0,[z1,z2,z1024,z3,z4,z171]),(0,[z1,z218,z3,z4,z694,z9]),(0,[z1,z2,z3,z1025,z4,z5]),(0,[z1,z2,z4,z338,z5,z6]),(0,[z1,z2,z3,z4,z145,z149]),(0,[z919,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z920,z11])],[(0,[z1,z2,z1026,z3,z4,z9]),(0,[z1,z2,z3,z4,z1027,z9]),(0,[z1,z8,z3,z268,z4,z9]),(0,[z1,z2,z633,z4,z5,z11]),(0,[z1,z3,z1028,z4,z5,z9]),(0,[z1,z2,z3,z4,z1029,z9])],[(0,[z1,z2,z3,z4,z5,z1030]),(0,[z1,z46,z107,z4,z5,z11]),(0,[z221,z2,z3,z4,z5,z38]),(0,[z1,z2,z3,z4,z5,z1031]),(0,[z1,z3,z4,z5,z9,z502]),(0,[z1,z2,z3,z1032,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z2,z3,z4,z5,z1034]),(0,[z1,z2,z3,z4,z186,z6]),(0,[z1,z2,z281,z3,z806,z9])],[(0,[z1,z3,z4,z5,z724,z9]),(0,[z1,z2,z1035,z3,z4,z5])],[(0,[z1,z2,z3,z4,z134,z6]),(0,[z1,z2,z1036,z3,z4,z9]),(0,[z1,z2,z103,z4,z5,z11]),(0,[z1,z2,z3,z4,z782,z9]),(0,[z1,z46,z150,z3,z4,z5]),(0,[z1,z930,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z1029,z6])],[(0,[z2,z797,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1037]),(0,[z1,z46,z3,z4,z5,z131]),(0,[z1,z2,z3,z69,z5,z12]),(0,[z1,z2,z1038,z3,z4,z5]),(0,[z1,z2,z4,z5,z776,z11]),(0,[z1,z2,z150,z3,z4,z589]),(0,[z1,z2,z3,z4,z5,z1039])],[(0,[z1,z754,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z2,z348,z43,z4,z5])],[(0,[z1,z2,z258,z4,z5,z11]),(0,[z1,z1040,z3,z4,z5,z9]),(0,[z1,z1041,z3,z4,z5,z9]),(0,[z1,z2,z1042,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z1043]),(0,[z1044,z2,z3,z4,z5,z9]),(0,[z1,z2,z17,z4,z133,z9])],[(0,[z309,z2,z107,z4,z5,z11]),(0,[z1,z2,z1045,z4,z5,z9]),(0,[z1,z2,z3,z130,z652,z5]),(0,[z1,z2,z3,z4,z1046,z9]),(0,[z1,z46,z3,z4,z5,z24])]],
   [[(0,[z1,z462,z3,z4,z340,z9]),(0,[z1,z2,z3,z1047,z4,z5]),(0,[z1,z2,z3,z4,z1048,z9]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z46,z150,z3,z4,z11])],[(0,[z1,z2,z3,z4,z5,z1050]),(0,[z1,z1051,z3,z4,z5,z9]),(0,[z1,z2,z3,z397,z152,z4]),(0,[z1,z2,z1052,z3,z4,z9]),(0,[z1,z2,z3,z117,z5,z6]),(0,[z1,z2,z3,z4,z5,z1053]),(0,[z1,z2,z3,z4,z5,z1054])],[(0,[z1,z2,z258,z4,z5,z38]),(0,[z1,z2,z348,z4,z5,z9]),(0,[z1,z2,z43,z4,z338,z5]),(0,[z1,z2,z3,z4,z5,z1055]),(0,[z1,z2,z17,z4,z133,z6])],[(0,[z1,z2,z3,z4,z5,z1056]),(0,[z1,z462,z3,z4,z5,z219]),(0,[z1,z2,z3,z4,z394,z9]),(0,[z1,z46,z3,z4,z167,z11]),(0,[z1,z2,z3,z4,z5,z1057]),(0,[z1,z2,z168,z4,z5,z11])],[(0,[z1,z2,z3,z397,z4,z5]),(0,[z1,z2,z1058,z4,z5,z9]),(0,[z329,z2,z3,z4,z5,z313]),(0,[z1,z2,z3,z1059,z5,z9]),(0,[z1,z2,z1060,z3,z4,z5]),(0,[z1,z2,z67,z3,z4,z167])],[(0,[z34,z1,z46,z3,z4,z5]),(0,[z1,z2,z67,z3,z4,z461]),(0,[z1,z2,z27,z30,z5,z9])],[(0,[z1,z2,z1061,z4,z5,z9]),(0,[z1,z1062,z3,z4,z5,z9]),(0,[z1,z2,z1063,z3,z4,z5]),(0,[z1,z713,z8,z3,z4,z5]),(0,[z1,z2,z348,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1064]),(0,[z1,z2,z3,z4,z394,z6]),(0,[z1,z1065,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1066]),(0,[z1,z2,z3,z4,z1067,z9]),(0,[z1,z2,z17,z4,z133,z18])]],
   [[(0,[z1,z2,z375,z4,z5,z11]),(0,[z1,z2,z3,z5,z9,z1068]),(0,[z1,z2,z3,z4,z9,z1069])],[(0,[z1,z2,z160,z4,z5,z725]),(0,[z1,z2,z1070,z4,z5,z9]),(0,[z1,z2,z61,z496,z3,z5]),(0,[z1,z2,z58,z4,z5,z11]),(0,[z1,z2,z27,z30,z5,z6]),(0,[z1,z2,z4,z5,z484,z11]),(0,[z1,z2,z3,z4,z47,z145])],[(0,[z1,z2,z1071,z4,z5,z9]),(0,[z110,z2,z3,z4,z5,z38]),(0,[z1,z2,z3,z4,z342,z313]),(0,[z1,z2,z3,z4,z1072,z5]),(0,[z1,z2,z3,z130,z5,z589]),(0,[z1,z2,z3,z4,z5,z1073]),(0,[z1,z2,z3,z5,z89,z843])],[(0,[z1,z462,z317,z4,z5,z9]),(0,[z140,z2,z3,z96,z356,z9]),(0,[z1,z2,z3,z1074,z4,z5]),(0,[z40,z2,z3,z4,z342,z9]),(0,[z1,z1075,z2,z3,z4,z5])],[(0,[z1,z75,z3,z4,z171,z9]),(0,[z36,z75,z3,z4,z5,z9]),(0,[z1,z2,z174,z3,z4,z11]),(0,[z1,z72,z73,z4,z5,z163])],[(0,[z1,z2,z61,z3,z144,z9]),(0,[z2,z3,z4,z21,z765,z9]),(0,[z121,z2,z3,z4,z5,z38])],[(0,[z1,z2,z1076,z3,z4,z9]),(0,[z1,z1077,z3,z4,z5,z9]),(0,[z1,z2,z317,z4,z5,z1078]),(0,[z1,z2,z496,z3,z4,z144]),(0,[z1,z2,z1079,z3,z4,z5]),(0,[z221,z1,z2,z3,z4,z182]),(0,[z39,z1,z136,z117,z5,z9]),(0,[z1,z1080,z2,z3,z4,z5]),(0,[z309,z2,z3,z4,z5,z488])],[(0,[z1,z2,z3,z1081,z5,z9]),(0,[z1,z2,z3,z1082,z5,z9]),(0,[z1,z3,z4,z5,z724,z63]),(0,[z1,z2,z27,z30,z5,z548]),(0,[z1,z1083,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1084,z9])]],
   [[(0,[z1,z462,z3,z4,z5,z11]),(0,[z1,z2,z160,z4,z5,z327]),(0,[z1,z2,z1085,z3,z4,z5]),(0,[z1,z2,z3,z4,z59,z5]),(0,[z1,z3,z4,z5,z9,z731]),(0,[z1,z2,z4,z818,z113,z9])],[(0,[z1,z2,z3,z4,z5,z1086]),(0,[z1,z2,z1087,z4,z5,z9]),(0,[z1,z2,z3,z4,z1088,z9]),(0,[z1,z2,z1007,z3,z4,z347]),(0,[z1,z2,z3,z4,z182,z89])],[(0,[z1,z2,z3,z4,z5,z1089]),(0,[z39,z1,z709,z4,z5,z9]),(0,[z1,z3,z4,z5,z9,z738]),(0,[z1,z966,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z11,z906]),(0,[z1,z2,z3,z4,z528,z145])],[(0,[z1,z1090,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z394,z131]),(0,[z39,z1,z631,z4,z5,z9])],[(0,[z1,z2,z3,z4,z1091,z9]),(0,[z1,z2,z3,z4,z5,z1092]),(0,[z39,z1,z136,z4,z394,z9]),(0,[z1,z2,z3,z4,z1093,z9]),(0,[z1,z2,z203,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1094])],[(0,[z1,z2,z3,z5,z9,z1095]),(0,[z1,z2,z3,z4,z727,z5]),(0,[z1,z1096,z3,z4,z5,z9]),(0,[z1,z2,z67,z3,z4,z48])],[(0,[z1,z2,z3,z4,z5,z1097]),(0,[z1,z2,z1098,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1099]),(0,[z1,z3,z4,z1100,z5,z9])],[(0,[z1,z2,z281,z3,z356,z9]),(0,[z1,z2,z574,z70,z5,z9]),(0,[z1,z2,z4,z5,z11,z432])]],
   [[(0,[z1,z2,z3,z1101,z5,z9]),(0,[z1,z2,z1102,z3,z5,z9]),(0,[z1,z2,z174,z95,z3,z4]),(0,[z1,z2,z4,z5,z9,z1103])],[(0,[z221,z2,z3,z4,z5,z438]),(0,[z1,z2,z150,z3,z4,z89])],[(0,[z185,z2,z107,z4,z5,z303]),(0,[z1,z2,z1104,z4,z5,z9]),(0,[z1,z1105,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z3,z155,z394,z9]),(0,[z1,z2,z105,z3,z5,z678])],[(0,[z7,z2,z61,z3,z62,z9]),(0,[z1,z2,z709,z4,z5,z9]),(0,[z1,z41,z3,z29,z186,z9]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z2,z249,z4,z5,z776]),(0,[z1,z2,z3,z4,z528,z247])],[(0,[z1,z2,z199,z4,z5,z764]),(0,[z34,z2,z3,z4,z5,z210]),(0,[z1,z2,z3,z4,z5,z1108]),(0,[z1,z2,z3,z4,z5,z1109]),(0,[z1,z2,z3,z4,z5,z1110]),(0,[z1,z2,z179,z4,z113,z51])],[(0,[z1,z2,z3,z4,z1111,z9]),(0,[z1,z2,z3,z4,z1112,z9]),(0,[z1,z2,z3,z4,z1113,z9]),(0,[z1,z2,z3,z4,z5,z1114])],[(0,[z1,z2,z3,z1115,z4,z9]),(0,[z1,z2,z67,z3,z4,z339])],[(0,[z1,z2,z1116,z3,z4,z5]),(0,[z1,z2,z17,z4,z818,z9]),(0,[z1,z46,z3,z4,z5,z11])]],
   [[(0,[z1,z471,z3,z42,z5,z9]),(0,[z1,z2,z1117,z3,z4,z9]),(0,[z1,z1118,z2,z3,z4,z5]),(0,[z1,z2,z1119,z3,z4,z9]),(0,[z1,z2,z3,z4,z1120,z9])],[(0,[z40,z2,z3,z4,z5,z9]),(0,[z1,z2,z61,z3,z109,z9]),(0,[z1,z2,z179,z4,z113,z9]),(0,[z1,z2,z3,z4,z6,z167])],[(0,[z1,z2,z3,z4,z1121,z9]),(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1,z2,z281,z3,z109,z9]),(1,[z1,z2,z3,z5,z843])],[(0,[z141,z2,z3,z116,z5,z9]),(0,[z1,z2,z3,z4,z5,z1122]),(0,[z1,z2,z3,z1123,z5,z9]),(0,[z1,z2,z348,z4,z113,z9]),(0,[z1,z46,z3,z4,z5,z502]),(0,[z1,z2,z4,z542,z5,z11])],[(0,[z329,z2,z3,z117,z5,z9]),(0,[z1,z2,z3,z4,z838,z9])],[(0,[z1,z2,z3,z4,z5,z1124]),(0,[z40,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z338,z5,z11]),(0,[z1,z54,z2,z150,z3,z4]),(0,[z1,z2,z179,z4,z113,z6]),(0,[z1,z2,z3,z4,z388,z167]),(0,[z1,z2,z3,z5,z843,z12])],[(0,[z1,z37,z160,z4,z5,z9]),(0,[z1,z2,z3,z4,z145,z137]),(0,[z1,z2,z281,z3,z109,z6])],[(0,[z1,z2,z1125,z3,z5,z9]),(0,[z0,z2,z199,z4,z5,z237]),(0,[z1,z2,z3,z4,z356,z11]),(0,[z1,z1126,z3,z4,z5,z9]),(0,[z2,z3,z712,z96,z5,z9]),(0,[z1,z709,z136,z4,z5,z9])]],
   [[(0,[z106,z75,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1127]),(0,[z1,z2,z3,z4,z1128,z9]),(0,[z1,z2,z3,z4,z186,z11]),(0,[z1,z2,z475,z4,z5,z6]),(0,[z1,z2,z207,z3,z5,z12]),(0,[z1,z1129,z3,z4,z5,z9]),(0,[z1,z2,z3,z130,z5,z89])],[(0,[z1,z2,z174,z3,z397,z4]),(0,[z1,z1130,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z1131]),(0,[z2,z199,z783,z4,z5,z9]),(0,[z1,z2,z3,z117,z342,z9]),(0,[z1,z3,z4,z782,z5,z9]),(0,[z1,z2,z3,z4,z298,z9]),(0,[z1,z46,z45,z4,z5,z11]),(0,[z1,z2,z1026,z3,z4,z11]),(0,[z1,z2,z3,z4,z5,z1132])],[(0,[z1,z2,z3,z4,z5,z1133]),(0,[z1,z2,z3,z4,z5,z327]),(0,[z1,z2,z3,z4,z182,z12]),(0,[z1,z634,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z1134]),(0,[z1,z2,z3,z4,z9,z167]),(0,[z1,z2,z3,z4,z47,z756])],[(0,[z106,z75,z3,z4,z5,z6]),(0,[z1,z2,z317,z4,z5,z1135]),(0,[z1,z2,z3,z4,z5,z1136]),(0,[z1,z948,z2,z3,z4,z5]),(0,[z1,z2,z4,z6,z167,z11])],[(0,[z1,z2,z3,z4,z5,z1137]),(0,[z1,z2,z179,z4,z342,z9])],[(0,[z1,z2,z61,z3,z5,z11]),(0,[z1,z2,z3,z4,z298,z6])],[(0,[z433,z2,z107,z4,z5,z9]),(0,[z1,z2,z3,z4,z1138,z5]),(0,[z1,z2,z348,z4,z342,z9]),(0,[z1,z2,z3,z4,z5,z1139])]],
   [[(0,[z1,z2,z3,z4,z891,z171]),(0,[z140,z1,z2,z174,z3,z9]),(0,[z1,z81,z3,z42,z5,z9]),(0,[z1,z218,z3,z4,z782,z9])],[(0,[z1,z2,z3,z4,z5,z1140]),(0,[z34,z2,z123,z4,z5,z210]),(0,[z40,z2,z3,z4,z5,z131]),(0,[z1,z98,z3,z4,z782,z9]),(0,[z1,z2,z3,z4,z5,z149]),(0,[z1,z2,z3,z4,z818,z9]),(0,[z1,z1040,z3,z4,z5,z11])],[(0,[z1,z2,z3,z4,z5,z1141]),(0,[z1,z2,z3,z4,z1142,z9]),(0,[z1,z2,z17,z4,z133,z11]),(0,[z1,z2,z3,z4,z5,z1143]),(0,[z1,z2,z150,z3,z4,z145])],[(0,[z1,z2,z1024,z3,z4,z5]),(0,[z1,z538,z2,z3,z4,z5]),(0,[z540,z26,z3,z4,z5,z9]),(0,[z141,z1,z2,z174,z3,z9]),(0,[z1144,z2,z3,z4,z5,z9]),(0,[z1,z2,z1145,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z157]),(0,[z1,z2,z150,z3,z4,z12])],[(0,[z1,z2,z422,z4,z5,z11]),(0,[z1,z2,z314,z4,z5,z11]),(0,[z1,z2,z3,z4,z1146,z9]),(0,[z1,z81,z3,z42,z5,z6]),(0,[z1,z2,z3,z4,z5,z1147]),(0,[z1,z2,z3,z4,z5,z1148]),(0,[z1,z2,z78,z70,z5,z157])],[(0,[z1,z2,z4,z5,z427,z11])],[(0,[z1,z2,z160,z4,z5,z9]),(0,[z7,z8,z3,z4,z62,z9]),(0,[z7,z1,z2,z61,z3,z9]),(0,[z1,z2,z61,z3,z277,z5]),(0,[z1,z2,z3,z4,z1149,z9]),(0,[z1,z2,z348,z4,z5,z11]),(0,[z1,z2,z150,z3,z4,z6]),(0,[z1,z2,z3,z4,z756,z48])],[(0,[z140,z462,z3,z96,z5,z9]),(0,[z1,z2,z3,z155,z5,z313]),(0,[z1,z2,z3,z4,z394,z11]),(0,[z1,z2,z3,z4,z1150,z9]),(0,[z1,z2,z596,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z1151]),(0,[z1,z419,z2,z150,z3,z4])]],
   [[(0,[z1,z2,z3,z4,z5,z1152]),(0,[z1,z8,z3,z4,z21,z9]),(0,[z40,z2,z3,z155,z5,z9]),(0,[z1,z2,z3,z1153,z5,z9])],[(0,[z1,z2,z3,z4,z134,z9]),(0,[z1,z26,z3,z4,z170,z9])],[(0,[z1,z2,z3,z4,z5,z1154]),(0,[z1,z2,z160,z4,z5,z6]),(0,[z1,z1155,z2,z3,z4,z5]),(0,[z1156,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1157])],[(0,[z1,z2,z107,z4,z5,z303]),(0,[z1,z462,z3,z4,z356,z9]),(0,[z1,z2,z3,z4,z5,z1158])],[(0,[z57,z26,z3,z4,z5,z11]),(0,[z1,z2,z496,z3,z4,z5]),(0,[z216,z2,z3,z4,z62,z9]),(0,[z1,z2,z3,z277,z364,z5]),(0,[z1,z2,z3,z4,z795,z11]),(0,[z1,z2,z3,z4,z9,z756])],[(0,[z1,z3,z4,z1159,z5,z9]),(0,[z1,z1160,z3,z4,z5,z9]),(0,[z221,z2,z3,z690,z4,z5]),(0,[z1,z2,z3,z4,z47,z298]),(0,[z1,z2,z3,z4,z5,z1161]),(0,[z1,z46,z4,z5,z6,z11])],[(0,[z1,z2,z3,z5,z1162,z9]),(0,[z1,z2,z3,z364,z5,z6]),(0,[z1,z2,z3,z4,z5,z1163])],[(0,[z1,z2,z3,z4,z755,z9])]],
   [[(0,[z1,z1164,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1135]),(0,[z1,z2,z3,z4,z1165,z9]),(0,[z1,z2,z3,z117,z5,z9]),(0,[z1,z2,z3,z102,z5,z589]),(0,[z1,z2,z3,z4,z5,z1166])],[(0,[z1,z37,z3,z4,z5,z9]),(0,[z1,z2,z317,z4,z5,z6]),(0,[z1,z646,z3,z4,z144,z9]),(0,[z1,z2,z17,z4,z9,z236]),(0,[z1,z2,z3,z5,z1068,z11]),(0,[z1,z2,z4,z5,z11,z529]),(0,[z1,z2,z3,z268,z142,z9]),(0,[z1,z2,z3,z4,z5,z1167])],[(0,[z1,z2,z3,z4,z5,z1168]),(0,[z2,z3,z4,z5,z9,z837])],[(0,[z1,z2,z3,z4,z1169,z9]),(0,[z1,z2,z3,z4,z5,z1170]),(0,[z7,z2,z670,z3,z4,z9]),(1,[z1,z2,z3,z806,z9])],[(0,[z39,z329,z136,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1171]),(0,[z1,z2,z3,z4,z5,z1172]),(0,[z1,z2,z179,z4,z113,z149]),(0,[z1,z3,z4,z167,z502,z11])],[(0,[z1,z37,z3,z4,z5,z6]),(0,[z1,z2,z3,z268,z142,z6])],[(0,[z1,z2,z150,z107,z4,z11]),(0,[z1,z2,z464,z4,z5,z11])],[(0,[z1,z2,z1173,z3,z5,z9]),(0,[z1,z3,z4,z5,z9,z868]),(0,[z1,z2,z67,z3,z4,z137])]],
   [[(0,[z1,z2,z3,z4,z5,z1174]),(0,[z1,z1175,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1176]),(0,[z1,z66,z3,z4,z5,z452]),(0,[z1,z46,z3,z4,z5,z241])],[(0,[z1,z2,z3,z4,z171,z9]),(0,[z1,z2,z3,z4,z5,z1177]),(0,[z1,z2,z3,z4,z5,z1178]),(0,[z1,z8,z3,z4,z5,z11]),(0,[z1,z1096,z3,z4,z5,z11]),(0,[z1,z2,z67,z3,z4,z465])],[(0,[z1,z1179,z3,z4,z5,z9]),(0,[z1,z2,z3,z1180,z5,z9]),(0,[z1,z3,z4,z1100,z5,z11])],[(0,[z185,z2,z107,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1181]),(0,[z1,z2,z3,z4,z5,z44]),(0,[z1,z2,z3,z4,z5,z1182]),(1,[z1,z46,z150,z3,z4])],[(0,[z1,z2,z3,z4,z5,z1183]),(0,[z1,z2,z3,z4,z1184,z9]),(0,[z1,z2,z3,z4,z5,z1185]),(0,[z1,z2,z3,z4,z394,z313]),(0,[z1,z2,z1186,z4,z5,z9]),(0,[z1,z2,z100,z4,z133,z9]),(0,[z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z1102,z3,z5,z11]),(0,[z443,z1,z2,z281,z3,z9])],[(0,[z1,z2,z3,z4,z171,z6]),(0,[z1,z2,z3,z4,z5,z1187]),(0,[z1,z2,z61,z3,z10,z9])],[(0,[z1,z2,z107,z4,z5,z157]),(0,[z1,z2,z1145,z4,z338,z5]),(0,[z1,z2,z3,z4,z47,z265])],[(0,[z185,z2,z107,z4,z5,z6]),(0,[z1,z2,z3,z4,z340,z327]),(0,[z1,z2,z1188,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z117,z5,z131]),(0,[z1,z2,z3,z4,z1189,z5])],[(0,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1190]),(0,[z34,z2,z258,z4,z5,z210]),(0,[z1,z73,z4,z5,z9,z256]),(0,[z1,z2,z3,z4,z1191,z9])],[(0,[z1,z2,z3,z4,z5,z1192]),(0,[z1,z2,z3,z4,z5,z1193]),(0,[z1,z1194,z3,z4,z5,z9]),(0,[z1,z46,z199,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z1195]),(0,[z1196,z2,z3,z4,z5,z9]),(0,[z1,z98,z3,z4,z10,z11]),(0,[z1,z2,z78,z70,z5,z9]),(0,[z1,z2,z17,z4,z133,z137])],[(0,[z1,z2,z3,z4,z918,z347])],[(0,[z1,z2,z1197,z4,z5,z9]),(0,[z1,z54,z3,z4,z204,z5])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1198]),(0,[z34,z2,z3,z4,z5,z851]),(0,[z40,z2,z3,z4,z5,z11]),(0,[z1,z2,z150,z3,z4,z149]),(0,[z1,z2,z179,z4,z113,z11]),(0,[z1,z2,z492,z4,z5,z11]),(0,[z1,z2,z3,z4,z1191,z6])],[(0,[z50,z26,z3,z4,z5,z9]),(0,[z1,z2,z1199,z4,z5,z9]),(0,[z1,z2,z78,z70,z5,z6]),(0,[z1,z2,z4,z133,z818,z9]),(0,[z1,z4,z5,z6,z502,z11]),(0,[z1,z2,z281,z3,z109,z11]),(0,[z1,z2,z3,z521,z5,z12])],[(0,[z1,z2,z3,z4,z1200,z9]),(0,[z1,z2,z3,z4,z5,z1201]),(0,[z141,z2,z3,z116,z5,z11]),(0,[z7,z2,z496,z3,z4,z62]),(0,[z1,z2,z3,z4,z5,z1202]),(0,[z1203,z2,z3,z4,z5,z9])]],
   [[],[(0,[z1,z2,z61,z3,z356,z9]),(0,[z1,z41,z3,z733,z5,z9])],[(0,[z1,z2,z3,z4,z1204,z9]),(0,[z1,z1205,z3,z4,z5,z9]),(0,[z1,z2,z160,z4,z340,z9]),(0,[z1,z2,z317,z4,z5,z327]),(0,[z1,z2,z3,z4,z5,z18])],[(0,[z1,z199,z4,z5,z502,z11]),(0,[z1,z2,z3,z4,z5,z548]),(1,[z1,z2,z734,z5,z9]),(0,[z1,z2,z70,z734,z5,z9]),(0,[z1,z988,z3,z4,z5,z11])],[(0,[z106,z75,z3,z4,z5,z11]),(0,[z264,z75,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1206,z9]),(0,[z1,z2,z3,z4,z1207,z9])],[(0,[z1,z2,z160,z4,z5,z219]),(0,[z1,z2,z3,z4,z47,z167])],[(0,[z1,z2,z3,z4,z5,z1208]),(0,[z1,z37,z3,z4,z5,z327]),(0,[z1,z2,z3,z4,z5,z1209]),(0,[z1,z2,z3,z4,z298,z11])],[(0,[z1,z122,z3,z4,z5,z9]),(0,[z1,z2,z3,z1210,z5,z9]),(0,[z1,z2,z3,z4,z5,z1211])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1047).take 187) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1234)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 524, 187] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 105).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 210).take 46).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [105, 105, 46] = true :=
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

end PEqualNP.Outside.L_meta_38685

theorem PEqualNP.Outside.L_meta_38685 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38685.solve