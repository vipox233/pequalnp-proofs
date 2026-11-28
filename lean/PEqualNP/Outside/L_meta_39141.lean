import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39141

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4205494272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000018615215578a#64 ++ 0x4000018615215578#64 ++ 0x5048b8e3f23fff8f#64 ++ 0xa5048b8e3f23fff8#64 : BitVec 256),
   (0x10930b2ccc3331bc#64 ++ 0x810930b2ccc3331b#64 ++ 0xf1b74f3ccc3333ff#64 ++ 0x7f1b74f3ccc3333f#64 : BitVec 256),
   (0x2638703706c3c2df#64 ++ 0x02638703706c3c2d#64 ++ 0x2e38703f0fc3c3fe#64 ++ 0xf2e38703f0fc3c3f#64 : BitVec 256),
   (0x8bc07dc00b7c0360#64 ++ 0x08bc07dc00b7c036#64 ++ 0xbfc07fc00ffc03fd#64 ++ 0xebfc07fc00ffc03f#64 : BitVec 256),
   (0x0dfd80000daaa800#64 ++ 0x00dfd80000daaa80#64 ++ 0xcfff80000ffffc0b#64 ++ 0xfcfff80000ffffc0#64 : BitVec 256),
   (0x4f6ee69aa0000000#64 ++ 0x04f6ee69aa000000#64 ++ 0xfffffffff0000007#64 ++ 0xffffffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000018615215578a 0x4000018615215578 0x100038e3f0000384 0x0100038e3f000038

def z1 : W := mkw 0x000018615215578a 0x4000018615215578 0x5048b8e3f23fff8f 0xa5048b8e3f23fff8

def z2 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfff80000ffffc0b 0xfcfff80000ffffc0

def z3 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1b74f3ccc3333ff 0x7f1b74f3ccc3333f

def z4 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e38703f0fc3c3fe 0xf2e38703f0fc3c3f

def z5 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffff0000007 0xffffffffff000000

def z6 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc07fc00ffc03fd 0xebfc07fc00ffc03f

def z7 : W := mkw 0x8bc07dc05b7c1760 0x48bc07dc05b7c176 0xffc0ffc0fffc3ffd 0xeffc0ffc0fffc3ff

def z8 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xbff77fdc00000005 0xfbff77fdc0000000

def z9 : W := mkw 0x109119655e3777be 0xc109119655e3777b 0x000000000e3ffff8 0x0000000000e3ffff

def z10 : W := mkw 0xc9c68fc8a93c0120 0x0c9c68fc8a93c012 0xd1c78fc0f03c0001 0x0d1c78fc0f03c000

def z11 : W := mkw 0x4f6ce49220000000 0x04f6ce4922000000 0xcfffb0c330000003 0xfcfffb0c33000000

def z12 : W := mkw 0x001000240403009c 0x0001000240403009 0x2030403c0c0303fe 0x72030403c0c0303f

def z13 : W := mkw 0x36bb7b3fcef3f3ff 0x836bb7b3fcef3f3f 0xffbf7f3fcff3f3ff 0xfffbf7f3fcff3f3f

def z14 : W := mkw 0x201000250483c09f 0x0201000250483c09 0x000000000003c000 0x0000000000003c00

def z15 : W := mkw 0x1dff9b6ddfbfffbe 0xc1dff9b6ddfbfffb 0xffffffffffffffff 0xffffffffffffffff

def z16 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x8fb700000dc00000 0x58fb700000dc0000

def z17 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xafb7471c00000000 0x5afb7471c0000000

def z18 : W := mkw 0x0010000404020014 0x0001000040402001 0x2030401c0c000070 0x52030401c0c00007

def z19 : W := mkw 0x1083030888202020 0x8108303088820202 0x8187070000000000 0x0818707000000000

def z20 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfbf80000dc3fc02 0x5cfbf80000dc3fc0

def z21 : W := mkw 0x8bc0658009680060 0x08bc065800968006 0xaf8047000dc00070 0x4af8047000dc0007

def z22 : W := mkw 0x8ffdfdc00ffeab60 0x08ffdfdc00ffeab6 0xffffffc00fffffff 0xfffffffc00ffffff

def z23 : W := mkw 0x008019615a3557aa 0x4008019615a3557a 0xf1c8ffe3fe3fffff 0xef1c8ffe3fe3ffff

def z24 : W := mkw 0x0200700002400240 0x0020070000240024 0x2e0070000fc003fc 0xe2e0070000fc003f

def z25 : W := mkw 0x1013022cc403309c 0x81013022cc403309 0x4037003cc0033002 0x14037003cc003300

def z26 : W := mkw 0x10130b2cc41331bc 0x810130b2cc41331b 0x70374f3cc00333f6 0x170374f3cc00333f

def z27 : W := mkw 0x000000215001548a 0x4000000215001548 0x40088023f003fc02 0x040088023f003fc0

def z28 : W := mkw 0x10930b0c8c322134 0x810930b0c8c32213 0xb1b74f1c0c3003fd 0x7b1b74f1c0c3003f

def z29 : W := mkw 0x0010000004020000 0x0001000000402000 0x003000000c03000a 0x7003000000c03000

def z30 : W := mkw 0x82807dc00a740360 0x082807dc00a74036 0xb1807fc00c3003fd 0x6b1807fc00c3003f

def z31 : W := mkw 0xbffb7fffcffff3ff 0x8bffb7fffcffff3f 0xffff7fffcffff3ff 0xfffff7fffcffff3f

def z32 : W := mkw 0x4f6eeebae0111188 0x04f6eeebae011118 0xfffffffff033338f 0xffffffffff033338

def z33 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xffc8ffc00fffffff 0xeffc8ffc00ffffff

def z34 : W := mkw 0x2628705312c4c643 0x42628705312c4c64 0x0e48b0c333cccc00 0x80e48b0c333cccc0

def z35 : W := mkw 0x0638700006c28240 0x00638700006c2824 0x2e3870000fc3c3fe 0xf2e3870000fc3c3f

def z36 : W := mkw 0x10830b08c8303120 0x810830b08c830312 0xd1870f00c0303001 0x0d1870f00c030300

def z37 : W := mkw 0x2628701302c0c243 0x02628701302c0c24 0x0e08300303c0c000 0x80e08300303c0c00

def z38 : W := mkw 0x8b407ce1535d57ca 0x48b407ce1535d57c 0x5e48b8e3f3ffff8f 0xa5e48b8e3f3ffff8

def z39 : W := mkw 0x0d7c800004828000 0x00d7c80000482800 0xcfff80000fc3c00b 0xfcfff80000fc3c00

def z40 : W := mkw 0xeffeffffafffc3ff 0x0effeffffafffc3f 0xffffffffffffc3ff 0xfffffffffffffc3f

def z41 : W := mkw 0x000000215001548a 0x4000000215001548 0x5048b8e3f003fc07 0xa5048b8e3f003fc0

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x40488000023ffc0b 0xa40488000023ffc0

def z43 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xbfb77ffff0000004 0x5bfb77ffff000000

def z44 : W := mkw 0x1002030c80000034 0x81002030c8000003 0x2000471c00000070 0x02000471c0000007

def z45 : W := mkw 0x2638701706c2c257 0x02638701706c2c25 0x2e38701f0fc0c070 0xd2e38701f0fc0c07

def z46 : W := mkw 0x2628703302c1c2cb 0x02628703302c1c2c 0x0e08302303c3c38e 0xa0e08302303c3c38

def z47 : W := mkw 0x5fffe79eac222034 0x85fffe79eac22203 0xfffffffffc000077 0xffffffffffc00007

def z48 : W := mkw 0x89c01dc00b7c0360 0x089c01dc00b7c036 0x91c00fc00ffc03f9 0x091c00fc00ffc03f

def z49 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xb1b74f3ccc0003f4 0x5b1b74f3ccc0003f

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0xb1804f0000000005 0x6b1804f000000000

def z51 : W := mkw 0x000018615215578a 0x4000018615215578 0x0000000000000380 0x0000000000000038

def z52 : W := mkw 0x0628601200000000 0x0062860120000000 0x7e78f8fff0000007 0xf7e78f8fff000000

def z53 : W := mkw 0x0d6c9861539ddf8a 0x40d6c9861539ddf8 0x5e48b8e3f3ffff8f 0xa5e48b8e3f3ffff8

def z54 : W := mkw 0x009100000daaa800 0x0009100000daaa80 0x000000000ffffc08 0x0000000000ffffc0

def z55 : W := mkw 0x4202669aa0000000 0x04202669aa000000 0x30007ffff0000004 0x030007ffff000000

def z56 : W := mkw 0x00021a69d215578a 0x400021a69d215578 0xf1fffffff23fff8f 0xff1fffffff23fff8

def z57 : W := mkw 0x0000184002140300 0x0000018400214030 0x104038c0023c038d 0xa104038c0023c038

def z58 : W := mkw 0x0080090008300120 0x0008009000830012 0xb1804f000c3003fd 0x6b1804f000c3003f

def z59 : W := mkw 0x9bd37feccf7f33fc 0x89bd37feccf7f33f 0xfff77ffccfff33ff 0xffff77ffccfff33f

def z60 : W := mkw 0x49468688a0000000 0x049468688a000000 0x8187070000000000 0x0818707000000000

def z61 : W := mkw 0x2638703756c3d6df 0x42638703756c3d6d 0x6e38f03fffc3fffe 0xf6e38f03fffc3fff

def z62 : W := mkw 0x0bc0648009280000 0x00bc064800928000 0xbfc07fc00ffc000d 0xebfc07fc00ffc000

def z63 : W := mkw 0x0f68649200000000 0x00f6864920000000 0xbff87fff00000007 0xfbff87fff0000000

def z64 : W := mkw 0x10020b2cc01111bc 0x810020b2cc01111b 0x30004f3cc00003f4 0x030004f3cc00003f

def z65 : W := mkw 0x10931b6dde3777be 0xc10931b6dde3777b 0xf1fffffffe3fffff 0xff1fffffffe3ffff

def z66 : W := mkw 0x1dff8b2ccc3331bc 0x81dff8b2ccc3331b 0xffffcf3ccc3333ff 0xfffffcf3ccc3333f

def z67 : W := mkw 0x89c019400b7c0360 0x089c019400b7c036 0x8fc000000ffc03f9 0xe8fc000000ffc03f

def z68 : W := mkw 0x4f6ef6bba201428a 0x04f6ef6bba201428 0xfffffffff203c38f 0xffffffffff203c38

def z69 : W := mkw 0x0d6c9041138cce02 0x40d6c9041138cce0 0x0e48b0c333cccc00 0x80e48b0c333cccc0

def z70 : W := mkw 0x4200649220000000 0x0420064922000000 0x000030c330000000 0x0000030c33000000

def z71 : W := mkw 0x10021b6dd21557be 0xc10021b6dd21557b 0x7048fffff23fffff 0xa7048fffff23ffff

def z72 : W := mkw 0x0438000004828000 0x0043800000482800 0x003800000003c002 0x1003800000003c00

def z73 : W := mkw 0x0002020880000000 0x0000202088000000 0xf1b74f3cc0000007 0x7f1b74f3cc000000

def z74 : W := mkw 0x5fffefbeec3331bc 0x85fffefbeec3331b 0xfffffffffc3333ff 0xffffffffffc3333f

def z75 : W := mkw 0x0b40748002400240 0x00b4074800240024 0xbfc07fc00fc003fd 0xebfc07fc00fc003f

def z76 : W := mkw 0x2638601604c28055 0x02638601604c2805 0x2e30401c0dc00070 0x52e30401c0dc0007

def z77 : W := mkw 0x0000084050141500 0x4000008405014150 0x504088c0f03c3c01 0x0504088c0f03c3c0

def z78 : W := mkw 0x043818615697d78a 0x4043818615697d78 0x5e78b8e3ffffff8f 0xf5e78b8e3ffffff8

def z79 : W := mkw 0x643e823fa483c09f 0x0643e823fa483c09 0x403f803ff003c002 0x1403f803ff003c00

def z80 : W := mkw 0x0000104112044602 0x4000010411204460 0x0048b0c3320ccc00 0x80048b0c3320ccc0

def z81 : W := mkw 0x1093030c8c222034 0x81093030c8c22203 0xa1b7471c0c000070 0x5a1b7471c0c00007

def z82 : W := mkw 0x1013020c84022014 0x81013020c8402201 0x0037001c00000000 0x10037001c0000000

def z83 : W := mkw 0x109109244c3331bc 0x8109109244c3331b 0x000000000c3333f8 0x0000000000c3333f

def z84 : W := mkw 0x6f7efefff6d7d7df 0x46f7efefff6d7d7d 0xffffffffffffffff 0xffffffffffffffff

def z85 : W := mkw 0x0d7d80000482a800 0x00d7d80000482a80 0xcfff80000003fc03 0xfcfff80000003fc0

def z86 : W := mkw 0x2638603604c380dd 0x02638603604c380d 0x2e30403c0dc303fe 0x72e30403c0dc303f

def z87 : W := mkw 0x8bc07de10b7d43ea 0x08bc07de10b7d43e 0xbfc87fe30fffc3ff 0xebfc87fe30fffc3f

def z88 : W := mkw 0x043d80000482a800 0x0043d80000482a80 0x403f80000003fc02 0x1403f80000003fc0

def z89 : W := mkw 0x0000184002140300 0x0000018400214030 0x5048b8e3f23c038f 0xa5048b8e3f23c038

def z90 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffff23ffc0f 0xffffffffff23ffc0

def z91 : W := mkw 0x4fffe69aadaaa800 0x04fffe69aadaaa80 0xfffffffffffffc0f 0xffffffffffffffc0

def z92 : W := mkw 0x49468688a0000000 0x049468688a000000 0xd1cfbfe3f0000007 0xad1cfbfe3f000000

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0x4048800000000003 0xa404880000000000

def z94 : W := mkw 0x043800240483809c 0x0043800240483809 0x2e38403c0fc3c3fe 0xf2e38403c0fc3c3f

def z95 : W := mkw 0x1dff8b2ccdbbb9bc 0x81dff8b2ccdbbb9b 0xffffcf3ccfffffff 0xfffffcf3ccffffff

def z96 : W := mkw 0x2638787756d7d7df 0x42638787756d7d7d 0x3e3878ffffc3c3fe 0xf3e3878ffffc3c3f

def z97 : W := mkw 0x062870330201428a 0x0062870330201428 0x2e38703f0203c38e 0xf2e38703f0203c38

def z98 : W := mkw 0x0628701202400240 0x0062870120240024 0x2e38703f0fc003fe 0xf2e38703f0fc003f

def z99 : W := mkw 0x442e821aa0000000 0x0442e821aa000000 0x403f803ff0000002 0x1403f803ff000000

def z100 : W := mkw 0x808019400b7c0360 0x0808019400b7c036 0x000000000ffc03f8 0x0000000000ffc03f

def z101 : W := mkw 0x14bb0b2cccb3b1bc 0x814bb0b2cccb3b1b 0xffbf4f3ccff3f3ff 0xfffbf4f3ccff3f3f

def z102 : W := mkw 0x82807dc00b7c0360 0x082807dc00b7c036 0x30007fc00ffc03fc 0x030007fc00ffc03f

def z103 : W := mkw 0x0628601200000000 0x0062860120000000 0x2e38703f00000006 0xf2e38703f0000000

def z104 : W := mkw 0x2010102506c3c2df 0x02010102506c3c2d 0x000000000fc3c3f8 0x0000000000fc3c3f

def z105 : W := mkw 0x8bc075800b680260 0x08bc075800b68026 0xaf8077000fc003fc 0xeaf8077000fc003f

def z106 : W := mkw 0x0438000004828000 0x0043800000482800 0x0e3800000fc3c00a 0xf0e3800000fc3c00

def z107 : W := mkw 0x0dfd89000dbaa920 0x00dfd89000dbaa92 0xffffcf000fffffff 0xfffffcf000ffffff

def z108 : W := mkw 0xaf7874f707cfc2df 0x0af7874f707cfc2d 0x2e7870ff0fcfc3fe 0xf2e7870ff0fcfc3f

def z109 : W := mkw 0x09c5800009282800 0x009c580000928280 0xc1cf8000023ffc0b 0xac1cf8000023ffc0

def z110 : W := mkw 0x1dff830c8daaa834 0x81dff830c8daaa83 0xafb7471c0dc00070 0x5afb7471c0dc0007

def z111 : W := mkw 0x0010000004828000 0x0001000000482800 0x000000000fc3c008 0x0000000000fc3c00

def z112 : W := mkw 0x10131a6dd617779e 0xc10131a6dd617779 0x507fb8fff23fff8f 0xb507fb8fff23fff8

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x0048b0c330000000 0x80048b0c33000000

def z114 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0x30004f3ccc3333fc 0x030004f3ccc3333f

def z115 : W := mkw 0x243818775697d79f 0x4243818775697d79 0x5078b8fff23fff8f 0xb5078b8fff23fff8

def z116 : W := mkw 0x0000004010040400 0x4000000401004040 0x004080c0300c0c00 0x0004080c0300c0c0

def z117 : W := mkw 0x8bc07de15b7d57ea 0x48bc07de15b7d57e 0xffc8ffe3ffffffff 0xeffc8ffe3fffffff

def z118 : W := mkw 0x22107037064342df 0x022107037064342d 0x2030703f0c0303fe 0x72030703f0c0303f

def z119 : W := mkw 0x0d6c800000000000 0x00d6c80000000000 0xcfff800000000003 0xfcfff80000000000

def z120 : W := mkw 0x49468688a0000000 0x049468688a000000 0xd1c78fc0f0000001 0x0d1c78fc0f000000

def z121 : W := mkw 0x8bc07dc11b7c4762 0x48bc07dc11b7c476 0xbfc8ffc33ffccffd 0xebfc8ffc33ffccff

def z122 : W := mkw 0x0944800000000000 0x0094480000000000 0xc1c7800000000001 0x0c1c780000000000

def z123 : W := mkw 0x02107024064302dc 0x002107024064302d 0x2e30703c0fc303fe 0xf2e30703c0fc303f

def z124 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1ffcf3cce3fffff 0xff1ffcf3cce3ffff

def z125 : W := mkw 0x109109244dbbb9bc 0x8109109244dbbb9b 0x000000000ffffff8 0x0000000000ffffff

def z126 : W := mkw 0x5fffe79eac222034 0x85fffe79eac22203 0xafb7471c0c000070 0x5afb7471c0c00007

def z127 : W := mkw 0x02007861525557ca 0x402007861525557c 0x7e48f8e3ffffffff 0xe7e48f8e3fffffff

def z128 : W := mkw 0x04bd80000daaa800 0x004bd80000daaa80 0x403f80000ffffc0a 0x1403f80000ffffc0

def z129 : W := mkw 0x0b407ce15215578a 0x40b407ce15215578 0xffc8ffe3f23fff8f 0xeffc8ffe3f23fff8

def z130 : W := mkw 0x10931b6dde3777be 0xc10931b6dde3777b 0xf1b77ffffc3333ff 0x7f1b77ffffc3333f

def z131 : W := mkw 0x009100000c222000 0x0009100000c22200 0xc1ff80000e3ffc0b 0xfc1ff80000e3ffc0

def z132 : W := mkw 0x000010210201428a 0x0000010210201428 0x000830230203c38e 0xa000830230203c38

def z133 : W := mkw 0x2638787756d7d7df 0x42638787756d7d7d 0x7e78f8ffffffffff 0xf7e78f8fffffffff

def z134 : W := mkw 0x10000924401111bc 0x810000924401111b 0x00000000000003f0 0x000000000000003f

def z135 : W := mkw 0x8bc5fdc00b7c2b60 0x08bc5fdc00b7c2b6 0xffc7ffc00ffc3ffd 0xeffc7ffc00ffc3ff

def z136 : W := mkw 0x1013022cc403309c 0x81013022cc403309 0x6037403ccc0333fe 0x76037403ccc0333f

def z137 : W := mkw 0x0dfd98615fbfff8a 0x40dfd98615fbfff8 0xdfffb8e3ffffff8f 0xfdfffb8e3ffffff8

def z138 : W := mkw 0x0000082040111188 0x0000008204011118 0x50000820c033338f 0x250000820c033338

def z139 : W := mkw 0x0002020880000000 0x0000202088000000 0xf1fffffff0000007 0xff1fffffff000000

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x5048b8e3f23ffc0f 0xa5048b8e3f23ffc0

def z141 : W := mkw 0x54bf8b3eec3331bc 0x854bf8b3eec3331b 0xf1bfcf3ffc3333ff 0x7f1bfcf3ffc3333f

def z142 : W := mkw 0x00020a28c0111188 0x000020a28c011118 0xf1b74f3cc033338f 0x7f1b74f3cc033338

def z143 : W := mkw 0x4fffe69aac222000 0x04fffe69aac22200 0xfffffffffc33300f 0xffffffffffc33300

def z144 : W := mkw 0x14bf8b2cccb3b9bc 0x814bf8b2cccb3b9b 0xf1bfcf3ccc33ffff 0x7f1bfcf3ccc33fff

def z145 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x8ff700000ffc0009 0xf8ff700000ffc000

def z146 : W := mkw 0x09c0000009280000 0x009c000000928000 0x8fc000000ffc0009 0xe8fc000000ffc000

def z147 : W := mkw 0x0000184002140300 0x0000018400214030 0x5048b8c0023fff8f 0xa5048b8c0023fff8

def z148 : W := mkw 0x0002020880000000 0x0000202088000000 0xd1870f00c0000001 0x0d1870f00c000000

def z149 : W := mkw 0x0000184002140300 0x0000018400214030 0x00000000023c0388 0x000000000023c038

def z150 : W := mkw 0x8ff87dc00ffe8360 0x08ff87dc00ffe836 0xbff87fc00fffc3ff 0xfbff87fc00fffc3f

def z151 : W := mkw 0x09c5800009282800 0x009c580000928280 0xc1c78000003c3c01 0x0c1c78000003c3c0

def z152 : W := mkw 0x001100000482a800 0x0001100000482a80 0x000000000003fc00 0x0000000000003fc0

def z153 : W := mkw 0x2010102506c3c2df 0x02010102506c3c2d 0x2030403c0fc3c3fe 0x72030403c0fc3c3f

def z154 : W := mkw 0x9bd3678c8d6a2074 0x89bd3678c8d6a207 0xafb7471c0dc00070 0x5afb7471c0dc0007

def z155 : W := mkw 0x0012022c8403009c 0x00012022c8403009 0xf1b74f3ccc0303ff 0x7f1b74f3ccc0303f

def z156 : W := mkw 0x4feeef9aa8300120 0x04feeef9aa830012 0xfffffffffc3003ff 0xffffffffffc3003f

def z157 : W := mkw 0x10930b08cc323120 0x810930b08cc32312 0xd1b70f00cc33300b 0x7d1b70f00cc33300

def z158 : W := mkw 0x0000084050141500 0x4000008405014150 0x5048b8e3f03c3c07 0xa5048b8e3f03c3c0

def z159 : W := mkw 0x0002020880000000 0x0000202088000000 0xa1b7471c00000000 0x5a1b7471c0000000

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0x504088c0f0000001 0x0504088c0f000000

def z161 : W := mkw 0x9bc27feccb7d13fc 0x89bc27feccb7d13f 0xbfc07ffccffc03fd 0xebfc07ffccffc03f

def z162 : W := mkw 0x009109000c322120 0x0009109000c32212 0xf1b74f000c3333ff 0x7f1b74f000c3333f

def z163 : W := mkw 0x028079000a700360 0x0028079000a70036 0xbf807f000ff003fd 0xebf807f000ff003f

def z164 : W := mkw 0x242800130080c003 0x0242800130080c00 0x000800030000c000 0x0000800030000c00

def z165 : W := mkw 0x109101040c222034 0x8109101040c22203 0x000000000c000070 0x0000000000c00007

def z166 : W := mkw 0x10020b2cc01111bc 0x810020b2cc01111b 0xf1b74f3cc00003f7 0x7f1b74f3cc00003f

def z167 : W := mkw 0x343b023fc483f09f 0x8343b023fc483f09 0x403f003fc003f002 0x1403f003fc003f00

def z168 : W := mkw 0x009100000daaa800 0x0009100000daaa80 0xc1b700000ffffc0b 0x7c1b700000ffffc0

def z169 : W := mkw 0x243800370483c09f 0x0243800370483c09 0x0038003f0003c002 0x10038003f0003c00

def z170 : W := mkw 0x89c00dc0093c0120 0x089c00dc0093c012 0x91c00fc0003c0001 0x091c00fc0003c000

def z171 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x6e78f03f0fffffff 0xf6e78f03f0ffffff

def z172 : W := mkw 0x10930b6cdc3735bc 0xc10930b6cdc3735b 0xf1f7cffcfc3f3fff 0x7f1f7cffcfc3f3ff

def z173 : W := mkw 0x0940000000000000 0x0094000000000000 0x8fc0000000000001 0xe8fc000000000000

def z174 : W := mkw 0x9bc37fc8cb7c3360 0x89bc37fc8cb7c336 0xffc77fc0cffc33fd 0xeffc77fc0cffc33f

def z175 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0x0e4030c00ffc03f8 0x80e4030c00ffc03f

def z176 : W := mkw 0x4ffde4922daaa800 0x04ffde4922daaa80 0xcfffb0c33ffffc0b 0xfcfffb0c33ffffc0

def z177 : W := mkw 0x4202669aa0000000 0x04202669aa000000 0xf1b77ffff0000007 0x7f1b77ffff000000

def z178 : W := mkw 0x10030208c0003000 0x810030208c000300 0x40070000c0003000 0x040070000c000300

def z179 : W := mkw 0x6f7ef6bfa6c3c2df 0x06f7ef6bfa6c3c2d 0xffffffffffc3c3ff 0xfffffffffffc3c3f

def z180 : W := mkw 0x0438000004828000 0x0043800000482800 0x0e3000000dc00000 0x50e3000000dc0000

def z181 : W := mkw 0x043d80000482a800 0x0043d80000482a80 0x407f8000023ffc0b 0xb407f8000023ffc0

def z182 : W := mkw 0x462a669aa0000000 0x0462a669aa000000 0x3e387ffff0000006 0xf3e387ffff000000

def z183 : W := mkw 0x4b42669aa0000000 0x04b42669aa000000 0xbfc07ffff0000005 0xebfc07ffff000000

def z184 : W := mkw 0x8bd07de40f7f03fc 0x08bd07de40f7f03f 0xbff07ffc0fff03ff 0xfbff07ffc0fff03f

def z185 : W := mkw 0x0000186042151388 0x0000018604215138 0x504038e0c23f338f 0xa504038e0c23f338

def z186 : W := mkw 0x8bc06d8009780160 0x08bc06d800978016 0xbf804f000df003fd 0x6bf804f000df003f

def z187 : W := mkw 0x22007037024142df 0x022007037024142d 0x2000703f000003f4 0x02000703f000003f

def z188 : W := mkw 0x2210702506c3c2df 0x02210702506c3c2d 0x2e0070000fc3c3fc 0xe2e0070000fc3c3f

def z189 : W := mkw 0x109119655e3777be 0xc109119655e3777b 0x5048b8e3fe3fffff 0xa5048b8e3fe3ffff

def z190 : W := mkw 0x263860370483c09f 0x0263860370483c09 0x2e38703f0003c006 0xf2e38703f0003c00

def z191 : W := mkw 0x8bd17dc00f7e2360 0x08bd17dc00f7e236 0xfff77fc00fff33ff 0xffff77fc00fff33f

def z192 : W := mkw 0x009100000c222000 0x0009100000c22200 0xc1b700000c33300b 0x7c1b700000c33300

def z193 : W := mkw 0x8b4074c0034c0240 0x08b4074c0034c024 0x0e4030c003cc0000 0x80e4030c003cc000

def z194 : W := mkw 0x2010186556d7d7df 0x42010186556d7d7d 0x000000000ffffff8 0x0000000000ffffff

def z195 : W := mkw 0x0000084050141500 0x4000008405014150 0x504888c0f23ffc0b 0xa504888c0f23ffc0

def z196 : W := mkw 0x000008615015558a 0x4000008615015558 0x504888e3f03ffc03 0x0504888e3f03ffc0

def z197 : W := mkw 0x0b40648000000000 0x00b4064800000000 0xbfc07fc000000005 0xebfc07fc00000000

def z198 : W := mkw 0xcfeeffdaab7c0360 0x0cfeeffdaab7c036 0xfffffffffffc03ff 0xffffffffffffc03f

def z199 : W := mkw 0x5ffffffffe3777be 0xc5ffffffffe3777b 0xfffffffffe3fffff 0xffffffffffe3ffff

def z200 : W := mkw 0x1093032c8c2320bc 0x81093032c8c2320b 0xa1b7473c0c0303fe 0x7a1b7473c0c0303f

def z201 : W := mkw 0x32937b3fce7373ff 0x832937b3fce7373f 0xf1b77f3fcc3333ff 0x7f1b77f3fcc3333f

def z202 : W := mkw 0x109109244c3331bc 0x8109109244c3331b 0xc1b700000c3333fb 0x7c1b700000c3333f

def z203 : W := mkw 0x4f6ce49220000000 0x04f6ce4922000000 0x0e48b0c330000000 0x80e48b0c33000000

def z204 : W := mkw 0x4f6efefbf215578a 0x44f6efefbf215578 0xfffffffff23fff8f 0xffffffffff23fff8

def z205 : W := mkw 0x5f6eefbee01111bc 0x85f6eefbee01111b 0xfffffffff00003f7 0xffffffffff00003f

def z206 : W := mkw 0x0000104112044602 0x4000010411204460 0x000030c330000000 0x0000030c33000000

def z207 : W := mkw 0x2ffdf0370febeadf 0x02ffdf0370febead 0xeffff03f0fffffff 0xfeffff03f0ffffff

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x5048b8e3f0000007 0xa5048b8e3f000000

def z209 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xdfffb8e3fffffc0f 0xfdfffb8e3fffffc0

def z210 : W := mkw 0x5fffefbeedbbb9bc 0x85fffefbeedbbb9b 0xffffffffffffffff 0xffffffffffffffff

def z211 : W := mkw 0x42027efbf215578a 0x442027efbf215578 0x7048fffff23fff8f 0xa7048fffff23fff8

def z212 : W := mkw 0x0000084050141500 0x4000008405014150 0x00000000003c3c00 0x000000000003c3c0

def z213 : W := mkw 0x09c5800009282800 0x009c580000928280 0xcfc780000ffc3c09 0xecfc780000ffc3c0

def z214 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbf807fc00dc003f4 0x4bf807fc00dc003f

def z215 : W := mkw 0x80000dc000140120 0x080000dc00014012 0x10000fc000000000 0x010000fc00000000

def z216 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xffc8ffe3fffc03ff 0xeffc8ffe3fffc03f

def z217 : W := mkw 0x101100244403309c 0x8101100244403309 0x0000000000033000 0x0000000000003300

def z218 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfff80000dc00003 0xfcfff80000dc0000

def z219 : W := mkw 0x0b40648000000000 0x00b4064800000000 0xaf80470000000000 0x4af8047000000000

def z220 : W := mkw 0x363a7b3fc6d3d3ff 0x8363a7b3fc6d3d3f 0x3e387f3fcfc3c3fe 0xf3e387f3fcfc3c3f

def z221 : W := mkw 0x82007dc002540360 0x082007dc00254036 0x30007fc0000003f4 0x030007fc0000003f

def z222 : W := mkw 0x4d6e821aa0000000 0x04d6e821aa000000 0xcfff803ff0000003 0xfcfff803ff000000

def z223 : W := mkw 0x0dfd80000c222000 0x00dfd80000c22200 0xcfff80000c33300b 0xfcfff80000c33300

def z224 : W := mkw 0x8bc07de15b7d57ea 0x48bc07de15b7d57e 0xbfc07fc00ffffffd 0xebfc07fc00ffffff

def z225 : W := mkw 0x4f7fe69aa482a800 0x04f7fe69aa482a80 0xfffffffff003fc07 0xffffffffff003fc0

def z226 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xdfcfbfc3f0000001 0x8dfcfbfc3f000000

def z227 : W := mkw 0x19c78b08c9383920 0x819c78b08c938392 0xd1c78f00c03c3c01 0x0d1c78f00c03c3c0

def z228 : W := mkw 0x0dff82088daaa800 0x00dff82088daaa80 0xffffcf3ccffffc0f 0xfffffcf3ccffffc0

def z229 : W := mkw 0x34bb0b3fccb3f1bf 0x834bb0b3fccb3f1b 0xf1bf4f3fcc33f3ff 0x7f1bf4f3fcc33f3f

def z230 : W := mkw 0x2638601604c28055 0x02638601604c2805 0x2e38401c0fc3c07a 0xf2e38401c0fc3c07

def z231 : W := mkw 0x0081000009282800 0x0008100000928280 0x00000000003c3c00 0x000000000003c3c0

def z232 : W := mkw 0x000010210201428a 0x0000010210201428 0x0000302300000384 0x0000030230000038

def z233 : W := mkw 0x0428000000808000 0x0042800000080800 0x0e08000003c0c000 0x80e08000003c0c00

def z234 : W := mkw 0x22007877525557df 0x422007877525557d 0x7048f8fff23fffff 0xa7048f8fff23ffff

def z235 : W := mkw 0x8fecfdc00b7c0360 0x08fecfdc00b7c036 0xffffffc00ffc03ff 0xfffffffc00ffc03f

def z236 : W := mkw 0x30931b2dcef3f3ff 0x830931b2dcef3f3f 0xf1b74f3ccff3f3ff 0x7f1b74f3ccff3f3f

def z237 : W := mkw 0x00820b0888300120 0x000820b088830012 0xf1b74f3ccc3003ff 0x7f1b74f3ccc3003f

def z238 : W := mkw 0x0000080040101100 0x0000008004010110 0x50000800c0303001 0x050000800c030300

def z239 : W := mkw 0x2f7cf03706c3c2df 0x02f7cf03706c3c2d 0xeffff03f0fc3c3ff 0xfeffff03f0fc3c3f

def z240 : W := mkw 0x2ff870370febc2df 0x02ff870370febc2d 0xaff8703f0fffc3ff 0xfaff8703f0fffc3f

def z241 : W := mkw 0x0000184152145702 0x4000018415214570 0x5048b8c3f23cfc01 0x85048b8c3f23cfc0

def z242 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0x4037003ccc3333fa 0x14037003ccc3333f

def z243 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfb700000df3300b 0x7cfb700000df3300

def z244 : W := mkw 0x89c0058009280020 0x089c005800928002 0x8180070000000000 0x0818007000000000

def z245 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e30401c0fc3c3f8 0x52e30401c0fc3c3f

def z246 : W := mkw 0x143f822cc483b89c 0x8143f822cc483b89 0x403f803cc003fc02 0x1403f803cc003fc0

def z247 : W := mkw 0x0000000110004402 0x4000000011000440 0x000880033000cc00 0x0000880033000cc0

def z248 : W := mkw 0x49468ec8f0141500 0x449468ec8f014150 0xd1c78fc0f03c3c01 0x0d1c78fc0f03c3c0

def z249 : W := mkw 0x1002022cc001109c 0x81002022cc001109 0x0000003cc0000000 0x00000003cc000000

def z250 : W := mkw 0x99c30fc8c93c3120 0x899c30fc8c93c312 0xd1c70fc0c03c3001 0x0d1c70fc0c03c300

def z251 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xffb74f3cc0000007 0x7ffb74f3cc000000

def z252 : W := mkw 0x36bb733f8ee3e2ff 0x836bb733f8ee3e2f 0xafbf773f0fc3c3fe 0xfafbf773f0fc3c3f

def z253 : W := mkw 0x0000000000000000 0x0000000000000000 0x2030403c00000006 0x72030403c0000000

def z254 : W := mkw 0x0080090008300120 0x0008009000830012 0x000000000c3003f8 0x0000000000c3003f

def z255 : W := mkw 0x000010215201568a 0x4000010215201568 0x4008b023f203ff8e 0xa4008b023f203ff8

def z256 : W := mkw 0x0dfd98400fbeab00 0x00dfd98400fbeab0 0xdfffb8c00fffff8f 0xfdfffb8c00fffff8

def z257 : W := mkw 0x263df03706c3eadf 0x0263df03706c3ead 0x6e3ff03f0fc3fffe 0xf6e3ff03f0fc3fff

def z258 : W := mkw 0xaff87df70fffc3ff 0x0aff87df70fffc3f 0xbff87fff0fffc3ff 0xfbff87fff0fffc3f

def z259 : W := mkw 0x5fffefbeec3331bc 0x85fffefbeec3331b 0xffb74f3ccc3333ff 0x7ffb74f3ccc3333f

def z260 : W := mkw 0x09c0090009380120 0x009c009000938012 0xbfc04f000ffc03fd 0xebfc04f000ffc03f

def z261 : W := mkw 0x8fe87dd20b7c0360 0x08fe87dd20b7c036 0xbff87fff0ffc03ff 0xfbff87fff0ffc03f

def z262 : W := mkw 0x22007037024142df 0x022007037024142d 0x2e00703f0fc003fc 0xe2e00703f0fc003f

def z263 : W := mkw 0x10830b08c8303120 0x810830b08c830312 0xf1b74f3cc0303007 0x7f1b74f3cc030300

def z264 : W := mkw 0xcf6cf4d2234c0240 0x0cf6cf4d2234c024 0x0e48b0c333cc0000 0x80e48b0c333cc000

def z265 : W := mkw 0x9bd37feddf7f77fe 0xc9bd37feddf7f77f 0xffffffffffffffff 0xffffffffffffffff

def z266 : W := mkw 0x4002021aa0000000 0x04002021aa000000 0x0000003ff0000000 0x00000003ff000000

def z267 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x7e78f8ffffc3c3ff 0xf7e78f8ffffc3c3f

def z268 : W := mkw 0x000018615215578a 0x4000018615215578 0x00083023023fff8e 0xa00083023023fff8

def z269 : W := mkw 0x000010210201428a 0x0000010210201428 0x000000000203c388 0x0000000000203c38

def z270 : W := mkw 0x894004c0010c0000 0x0894004c0010c000 0x004000c0000c0000 0x0004000c0000c000

def z271 : W := mkw 0x009100000daaa800 0x0009100000daaa80 0x000000000dc00000 0x0000000000dc0000

def z272 : W := mkw 0x2010000404c28055 0x02010000404c2805 0x000000000dc00070 0x0000000000dc0007

def z273 : W := mkw 0x82007de1525557ea 0x482007de1525557e 0x30007fe3f00003f4 0x030007fe3f00003f

def z274 : W := mkw 0x0b40648000000000 0x00b4064800000000 0xffc8ffe3f0000007 0xeffc8ffe3f000000

def z275 : W := mkw 0x4f6ee6bbf001548a 0x44f6ee6bbf001548 0xfffffffff003fc07 0xffffffffff003fc0

def z276 : W := mkw 0x009100000c222000 0x0009100000c22200 0x000000000c333008 0x0000000000c33300

def z277 : W := mkw 0x4dff8688adaaa800 0x04dff8688adaaa80 0xdfff8fc0fffffc0b 0xfdfff8fc0fffffc0

def z278 : W := mkw 0x0df800000daa8000 0x00df800000daa800 0x8ff800000fffc00b 0xf8ff800000fffc00

def z279 : W := mkw 0x1093030c8c222034 0x81093030c8c22203 0xf1b74f3ccc000077 0x7f1b74f3ccc00007

def z280 : W := mkw 0x4b46e69aa0000000 0x04b46e69aa000000 0xf1c7fffff0000005 0x0f1c7fffff000000

def z281 : W := mkw 0x4fffe69aadaaa800 0x04fffe69aadaaa80 0xafb7471c0dc00000 0x5afb7471c0dc0000

def z282 : W := mkw 0x6f6ef69ba2c0c243 0x06f6ef69ba2c0c24 0xfffffffff3c0c007 0xffffffffff3c0c00

def z283 : W := mkw 0x000000215001548a 0x4000000215001548 0x00000023f0000000 0x000000023f000000

def z284 : W := mkw 0xcfeee79aa9680060 0x0cfeee79aa968006 0xfffffffffdc00077 0xffffffffffdc0007

def z285 : W := mkw 0x10831b69da3577aa 0xc10831b69da3577a 0xd1cfbfe3f23fff8f 0xad1cfbfe3f23fff8

def z286 : W := mkw 0x1dff8b08cdbab920 0x81dff8b08cdbab92 0xdfff8f00cffffc0b 0xfdfff8f00cffffc0

def z287 : W := mkw 0x1dfd89244dbbb9bc 0x81dfd89244dbbb9b 0xcfff80000ffffffb 0xfcfff80000ffffff

def z288 : W := mkw 0x109109244c3331bc 0x8109109244c3331b 0xb1804f000c3333fd 0x6b1804f000c3333f

def z289 : W := mkw 0x2010102506c3c2df 0x02010102506c3c2d 0x000830230fc3c3fe 0xa000830230fc3c3f

def z290 : W := mkw 0x4202669aa0000000 0x04202669aa000000 0x7048fffff0000007 0xa7048fffff000000

def z291 : W := mkw 0x4f6ce49221888800 0x04f6ce4922188880 0x0e48b0c333cccc00 0x80e48b0c333cccc0

def z292 : W := mkw 0x0dfd88204dbbb988 0x00dfd88204dbbb98 0xdfff8820cfffff8f 0xfdfff8820cfffff8

def z293 : W := mkw 0x2628701302c0c243 0x02628701302c0c24 0x2e0870030fc0c3fc 0xe2e0870030fc0c3f

def z294 : W := mkw 0x0d7c8000058a8800 0x00d7c8000058a880 0x0e7880000fcfcc0a 0xf0e7880000fcfcc0

def z295 : W := mkw 0x6f7cf4b726c3c2df 0x06f7cf4b726c3c2d 0x2e78f0ff3fc3c3fe 0xf2e78f0ff3fc3c3f

def z296 : W := mkw 0x2210703706c3c2df 0x02210703706c3c2d 0x2000703f0fc3c3fc 0x02000703f0fc3c3f

def z297 : W := mkw 0x000018214211538a 0x0000018214211538 0x50083823c233f38f 0xa50083823c233f38

def z298 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x0e4880000ffffc08 0x80e4880000ffffc0

def z299 : W := mkw 0x2200601600400055 0x0220060160040005 0x2000401c00000070 0x02000401c0000007

def z300 : W := mkw 0x8f6cf4c003cc8a40 0x08f6cf4c003cc8a4 0x0e48b0c003cccc00 0x80e48b0c003cccc0

def z301 : W := mkw 0x000018615215578a 0x4000018615215578 0x50000820c23fff8f 0x250000820c23fff8

def z302 : W := mkw 0x0628601200000000 0x0062860120000000 0x0e08300300000000 0x80e0830030000000

def z303 : W := mkw 0x063860360403009c 0x0063860360403009 0x2e38703f0c0303fe 0xf2e38703f0c0303f

def z304 : W := mkw 0x4d6e869aa0000000 0x04d6e869aa000000 0xd1ff8ffff0000003 0x1d1ff8ffff000000

def z305 : W := mkw 0x4f6ce49220000000 0x04f6ce4922000000 0x2e78f0ff30000006 0xf2e78f0ff3000000

def z306 : W := mkw 0x8bc0658009680060 0x08bc065800968006 0xafc047000ffc0079 0xeafc047000ffc007

def z307 : W := mkw 0x442e823bf001548a 0x4442e823bf001548 0x403f803ff003fc02 0x1403f803ff003fc0

def z308 : W := mkw 0x042c800000808800 0x0042c80000080880 0x000880000000cc00 0x0000880000000cc0

def z309 : W := mkw 0x82007dc002540360 0x082007dc00254036 0x3e007fc00fc003fc 0xe3e007fc00fc003f

def z310 : W := mkw 0x10820b2cc83111bc 0x810820b2cc83111b 0xb1804f3ccc3003fd 0x6b1804f3ccc3003f

def z311 : W := mkw 0x263a723f86c3c2df 0x0263a723f86c3c2d 0xffbf7f3fcfc3c3ff 0xfffbf7f3fcfc3c3f

def z312 : W := mkw 0x8ffdf4c00feeaa40 0x08ffdf4c00feeaa4 0xcfffb0c00ffffc0b 0xfcfffb0c00ffffc0

def z313 : W := mkw 0x22007037024142df 0x022007037024142d 0x2008703f0203c3fe 0xa2008703f0203c3f

def z314 : W := mkw 0x0d6c98615215578a 0x40d6c98615215578 0xdfffb8e3f23fff8f 0xfdfffb8e3f23fff8

def z315 : W := mkw 0x000018615215578a 0x4000018615215578 0x100038e3f23fff8c 0x0100038e3f23fff8

def z316 : W := mkw 0x909119644f7f33fc 0x8909119644f7f33f 0x000000000fff33f8 0x0000000000fff33f

def z317 : W := mkw 0x09c58840593c3d00 0x409c58840593c3d0 0xd1c788c0f03c3c01 0x0d1c788c0f03c3c0

def z318 : W := mkw 0x000000215001548a 0x4000000215001548 0x000000000003fc00 0x0000000000003fc0

def z319 : W := mkw 0x0d6e820880000000 0x00d6e82088000000 0xffffcf3cc0000007 0xfffffcf3cc000000

def z320 : W := mkw 0x2ffdf0370febeadf 0x02ffdf0370febead 0xafbf703f0fc3c3fe 0xfafbf703f0fc3c3f

def z321 : W := mkw 0x0d6c800001888800 0x00d6c80000188880 0x0e48800003cccc00 0x80e48800003cccc0

def z322 : W := mkw 0x0080090008300120 0x0008009000830012 0x91800f0000300001 0x091800f000030000

def z323 : W := mkw 0xcfeee79aa9680060 0x0cfeee79aa968006 0xafb7471c0dc00070 0x5afb7471c0dc0007

def z324 : W := mkw 0x1013022cc403309c 0x81013022cc403309 0xf1b74f3cc0033007 0x7f1b74f3cc003300

def z325 : W := mkw 0x09c0000009280000 0x009c000000928000 0xcfc880000ffffc0b 0xecfc880000ffffc0

def z326 : W := mkw 0x89c58dc0093c2920 0x089c58dc0093c292 0xd1c78fc0003c3c01 0x0d1c78fc0003c3c0

def z327 : W := mkw 0x8bc27fc88b7c0360 0x08bc27fc88b7c036 0xfff77ffccffc03ff 0xffff77ffccffc03f

def z328 : W := mkw 0x009009240c3301bc 0x0009009240c3301b 0xb1b04f3c0c3303ff 0x7b1b04f3c0c3303f

def z329 : W := mkw 0x1093030c8c222034 0x81093030c8c22203 0xe1b7471c0c33307b 0x7e1b7471c0c33307

def z330 : W := mkw 0x0200700002400240 0x0020070000240024 0x20007000000003f4 0x020007000000003f

def z331 : W := mkw 0x828079400b7c0360 0x0828079400b7c036 0x2e0070000ffc03fc 0xe2e0070000ffc03f

def z332 : W := mkw 0x0bc06d8008300120 0x00bc06d800830012 0xbfc07fc00c3003fd 0xebfc07fc00c3003f

def z333 : W := mkw 0x009118615fbfff8a 0x4009118615fbfff8 0x000000000fffff88 0x0000000000fffff8

def z334 : W := mkw 0x0000082040111188 0x0000008204011118 0x10000820c0000384 0x010000820c000038

def z335 : W := mkw 0x243800375483d49f 0x4243800375483d49 0x4038803ff003fc02 0x14038803ff003fc0

def z336 : W := mkw 0x8bc0658009680060 0x08bc065800968006 0xbfc07fc00dc00075 0xebfc07fc00dc0007

def z337 : W := mkw 0x043d80000482a800 0x0043d80000482a80 0x4e3f80000fc3fc0a 0xf4e3f80000fc3fc0

def z338 : W := mkw 0x001010250603429e 0x0001010250603429 0x2038703f0e03c3fe 0xf2038703f0e03c3f

def z339 : W := mkw 0x042c800000000000 0x0042c80000000000 0x403f800000000002 0x1403f80000000000

def z340 : W := mkw 0x5fefef9ae8303120 0x85fefef9ae830312 0xfffffffff0303007 0xffffffffff030300

def z341 : W := mkw 0x620276bfa24142df 0x0620276bfa24142d 0x30007ffff00003f4 0x030007ffff00003f

def z342 : W := mkw 0x000018615215578a 0x4000018615215578 0x00000000023fff88 0x000000000023fff8

def z343 : W := mkw 0x22007877525557df 0x422007877525557d 0x300078fff00003f4 0x0300078fff00003f

def z344 : W := mkw 0x0944800001080800 0x0094480000108080 0x00408000000c0c00 0x000408000000c0c0

def z345 : W := mkw 0x200000370001409f 0x0200000370001409 0x0000003f00000000 0x00000003f0000000

def z346 : W := mkw 0x26b970370febeadf 0x026b970370febead 0x2e38703f0ffffffe 0xf2e38703f0ffffff

def z347 : W := mkw 0x0b40648000000000 0x00b4064800000000 0x0e4030c000000000 0x80e4030c00000000

def z348 : W := mkw 0x0428001200000000 0x0042800120000000 0x0038003f00000002 0x10038003f0000000

def z349 : W := mkw 0xa09019650fffc3ff 0x0a09019650fffc3f 0x000000000fffc3f8 0x0000000000fffc3f

def z350 : W := mkw 0x26b879370ef3c3ff 0x026b879370ef3c3f 0xbfb87f3f0ff3c3ff 0xfbfb87f3f0ff3c3f

def z351 : W := mkw 0x8bc074c00b6c0240 0x08bc074c00b6c024 0x8fc030c00ffc0009 0xe8fc030c00ffc000

def z352 : W := mkw 0x8dfd8dc00dbea920 0x08dfd8dc00dbea92 0xdfff8fc00ffffc0b 0xfdfff8fc00ffffc0

def z353 : W := mkw 0x1013022dd403749e 0xc1013022dd403749 0x403f803ff003fc02 0x1403f803ff003fc0

def z354 : W := mkw 0x0d6c800001888800 0x00d6c80000188880 0x4e48800003fffc0b 0xa4e48800003fffc0

def z355 : W := mkw 0x2638701606c28255 0x02638701606c2825 0x2e30701c0fc003fc 0xf2e30701c0fc003f

def z356 : W := mkw 0x663a76bfa6c3c2df 0x0663a76bfa6c3c2d 0x3e387fffffc3c3fe 0xf3e387fffffc3c3f

def z357 : W := mkw 0x2628703702c1c2df 0x02628703702c1c2d 0x2e08703f03c0c3f4 0x82e08703f03c0c3f

def z358 : W := mkw 0x4f7ee69aa4828000 0x04f7ee69aa482800 0xffffffffffc3c00f 0xfffffffffffc3c00

def z359 : W := mkw 0x000018615215578a 0x4000018615215578 0x40088023f23fff8a 0x040088023f23fff8

def z360 : W := mkw 0x0002020880000000 0x0000202088000000 0x30004f3cc0000004 0x030004f3cc000000

def z361 : W := mkw 0x4f6ee69aa1888800 0x04f6ee69aa188880 0xfffffffff3cccc07 0xffffffffff3cccc0

def z362 : W := mkw 0x663ef23fa6c3c2df 0x0663ef23fa6c3c2d 0x6e3ff03fffc3c3fe 0xf6e3ff03fffc3c3f

def z363 : W := mkw 0x9bd36faccd7b31fc 0x89bd36faccd7b31f 0xffb74f3ccdf333ff 0x7ffb74f3ccdf333f

def z364 : W := mkw 0x0428000000000000 0x0042800000000000 0x0e38000000000002 0xf0e3800000000000

def z365 : W := mkw 0x0438000004828000 0x0043800000482800 0x4e7880000ffffc0b 0xf4e7880000ffffc0

def z366 : W := mkw 0x0011000004022000 0x0001100000402200 0x4037000000033002 0x1403700000003300

def z367 : W := mkw 0x043d80215483fc8a 0x4043d80215483fc8 0x403f8023f003fc02 0x1403f8023f003fc0

def z368 : W := mkw 0x10930b0ccc323134 0x810930b0ccc32313 0xf1b74f1ccc303071 0x5f1b74f1ccc30307

def z369 : W := mkw 0x109109244c3331bc 0x8109109244c3331b 0x50000820cc3333ff 0x250000820cc3333f

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x200040000c0003fc 0x6200040000c0003f

def z371 : W := mkw 0x8bc06dc0093c0120 0x08bc06dc0093c012 0xbfc07fc0003c0005 0xebfc07fc0003c000

def z372 : W := mkw 0x462ee21aa0000000 0x0462ee21aa000000 0x6e3ff03ff0000006 0xf6e3ff03ff000000

def z373 : W := mkw 0x8ffde5800deaa860 0x08ffde5800deaa86 0xefffc7000ffffc7b 0xfefffc7000ffffc7

def z374 : W := mkw 0x8000194002540360 0x0800019400254036 0x00000000000003f0 0x000000000000003f

def z375 : W := mkw 0x009118615fbfff8a 0x4009118615fbfff8 0x5048b8e3ffffff8f 0xa5048b8e3ffffff8

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000023ffc08 0x000000000023ffc0

def z377 : W := mkw 0x0000000050001400 0x4000000005000140 0x40008000f0003c00 0x040008000f0003c0

def z378 : W := mkw 0x2438001604828015 0x0243800160482801 0x0030001c00000000 0x10030001c0000000

def z379 : W := mkw 0x0d6c800000000000 0x00d6c80000000000 0x8fb7000000000000 0x58fb700000000000

def z380 : W := mkw 0x4feee69aa9280000 0x04feee69aa928000 0xfffffffffffc000f 0xffffffffffffc000

def z381 : W := mkw 0xa2007df7025543ff 0x0a2007df7025543f 0x30007fff000003f4 0x030007fff000003f

def z382 : W := mkw 0x09c018400b3c0300 0x009c018400b3c030 0x9fc038c00ffc038d 0xe9fc038c00ffc038

def z383 : W := mkw 0x19d30b2ccd3b31bc 0x819d30b2ccd3b31b 0xfff74f3ccfff33ff 0xffff74f3ccfff33f

def z384 : W := mkw 0x10830b48d8343520 0xc10830b48d834352 0xd1c78fc0f03c3c01 0x0d1c78fc0f03c3c0

def z385 : W := mkw 0x2638601604c28055 0x02638601604c2805 0x2e38703f0dc00076 0xf2e38703f0dc0007

def z386 : W := mkw 0x0000080000100100 0x0000008000010010 0x100008000030038d 0x2100008000030038

def z387 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xa1b7471c0c3333f8 0x5a1b7471c0c3333f

def z388 : W := mkw 0x8b407dc002540360 0x08b407dc00254036 0xbfc07fc0000003f5 0xebfc07fc0000003f

def z389 : W := mkw 0x0000184112144702 0x4000018411214470 0x1048b8c3323ccf8d 0xa1048b8c3323ccf8

def z390 : W := mkw 0x36bb7b7fdef7f7ff 0xc36bb7b7fdef7f7f 0xffffffffffffffff 0xffffffffffffffff

def z391 : W := mkw 0x0dfd90210fabea8a 0x00dfd90210fabea8 0xcfffb0230fffff8f 0xfcfffb0230fffff8

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008302300000006 0xa000830230000000

def z393 : W := mkw 0x243810370683c29f 0x0243810370683c29 0x0038303f0203c38e 0xb0038303f0203c38

def z394 : W := mkw 0x8200658000400060 0x0820065800040006 0x2000470000000070 0x0200047000000007

def z395 : W := mkw 0x0d7d8000058aa800 0x00d7d8000058aa80 0x4e7f800003cffc02 0x94e7f800003cffc0

def z396 : W := mkw 0x4fffe69aadaaa800 0x04fffe69aadaaa80 0xfffffffffdc00007 0xffffffffffdc0000

def z397 : W := mkw 0x4f6ef69aa2400240 0x04f6ef69aa240024 0xffffffffffc003ff 0xfffffffffffc003f

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x00488000020ccc00 0x800488000020ccc0

def z399 : W := mkw 0x008019400a340320 0x0008019400a34032 0xb1c07fc00e3c03fd 0xeb1c07fc00e3c03f

def z400 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1fffffffc3333ff 0xff1fffffffc3333f

def z401 : W := mkw 0x000000240001009c 0x0000000240001009 0x2000403c000003f4 0x02000403c000003f

def z402 : W := mkw 0x2f6cf01303c8ca43 0x02f6cf01303c8ca4 0x0e48b00303cccc00 0x80e48b00303cccc0

def z403 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xd1b70f3cc0333003 0x1d1b70f3cc033300

def z404 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xefffc71c00000003 0xfefffc71c0000000

def z405 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x8fbf00000fc3c00a 0xf8fbf00000fc3c00

def z406 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xaf8047000ffc03f8 0x4af8047000ffc03f

def z407 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x0e38303f03c3c002 0x90e38303f03c3c00

def z408 : W := mkw 0xaff87df75fffd7ff 0x4aff87df75fffd7f 0xfff8ffffffffffff 0xffff8fffffffffff

def z409 : W := mkw 0xc2027fdaa2540360 0x0c2027fdaa254036 0x30007ffff00003f4 0x030007ffff00003f

def z410 : W := mkw 0xcfeefffbfb7d57ea 0x4cfeefffbfb7d57e 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x10120b2cc41311bc 0x810120b2cc41311b 0x30304f3ccc0303fe 0x730304f3ccc0303f

def z412 : W := mkw 0x000018615215578a 0x4000018615215578 0x104038e3f23c038d 0xa104038e3f23c038

def z413 : W := mkw 0x8ffdfde15fffffea 0x48ffdfde15fffffe 0xffffffe3ffffffff 0xfffffffe3fffffff

def z414 : W := mkw 0x89c00dc0093c0120 0x089c00dc0093c012 0xb1c04fc00c3c03fd 0x6b1c04fc00c3c03f

def z415 : W := mkw 0x243800370483c09f 0x0243800370483c09 0x2038403f0c03c3fe 0x72038403f0c03c3f

def z416 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000820c0000007 0x250000820c000000

def z417 : W := mkw 0x1dff822ccdabb89c 0x81dff822ccdabb89 0xcfff803ccffffc0b 0xfcfff803ccffffc0

def z418 : W := mkw 0x10830b08c8303120 0x810830b08c830312 0xf1874f00cc3033fd 0x6f1874f00cc3033f

def z419 : W := mkw 0x0d6c800000000000 0x00d6c80000000000 0xdfffb8e3f0000007 0xfdfffb8e3f000000

def z420 : W := mkw 0x4fefe69aa9282800 0x04fefe69aa928280 0xfffffffff03c3c07 0xffffffffff03c3c0

def z421 : W := mkw 0x8b407dc0035c0360 0x08b407dc0035c036 0x3e407fc003cc03f4 0x83e407fc003cc03f

def z422 : W := mkw 0x10930b2ccdbbb9bc 0x810930b2ccdbbb9b 0xf1b74f3ccfffffff 0x7f1b74f3ccffffff

def z423 : W := mkw 0x8dfd99400ffeab60 0x08dfd99400ffeab6 0xcfff80000ffffffb 0xfcfff80000ffffff

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x100038e3f0000004 0x0100038e3f000000

def z425 : W := mkw 0x2638603704c3c0df 0x02638603704c3c0d 0x2e38403f0dc3c072 0x52e38403f0dc3c07

def z426 : W := mkw 0x0080000008200000 0x0008000000820000 0x818000000c300009 0x6818000000c30000

def z427 : W := mkw 0x4f6efedaa2140300 0x04f6efedaa214030 0xfffffffff23c038f 0xffffffffff23c038

def z428 : W := mkw 0x0dfd80240daba89c 0x00dfd80240daba89 0xefffc03c0fffffff 0xfefffc03c0ffffff

def z429 : W := mkw 0x043810210683c28a 0x0043810210683c28 0x0e3830230fc3c38e 0xf0e3830230fc3c38

def z430 : W := mkw 0x0000184002140300 0x0000018400214030 0x100038c000000384 0x0100038c00000038

def z431 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xc1ff8000003ffc03 0x1c1ff8000003ffc0

def z432 : W := mkw 0x4202669aa0000000 0x04202669aa000000 0x2000471c00000000 0x02000471c0000000

def z433 : W := mkw 0x89c01dc00b3c0320 0x089c01dc00b3c032 0x91c03fc0023c038d 0xa91c03fc0023c038

def z434 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e30703f0dc003f4 0x52e30703f0dc003f

def z435 : W := mkw 0x4f6cfcf37215578a 0x44f6cfcf37215578 0x5e48b8e3f23fff8f 0xa5e48b8e3f23fff8

def z436 : W := mkw 0x0ffde0120daaa800 0x00ffde0120daaa80 0xeffff03f0ffffc0f 0xfeffff03f0ffffc0

def z437 : W := mkw 0x10931b6cce3733bc 0x810931b6cce3733b 0xf1f77ffcce3f33ff 0xff1f77ffcce3f33f

def z438 : W := mkw 0x6f6ef6bfa24142df 0x06f6ef6bfa24142d 0xfffffffff00003f7 0xffffffffff00003f

def z439 : W := mkw 0x462ee69aa0000000 0x0462ee69aa000000 0x703ffffff0000006 0x1703ffffff000000

def z440 : W := mkw 0x4b46e688a0000000 0x04b46e688a000000 0xffc7ffc0f0000005 0xeffc7ffc0f000000

def z441 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0x3e48fffff0000004 0x83e48fffff000000

def z442 : W := mkw 0x0940000001080000 0x0094000000108000 0x0e40000003cc0000 0x80e40000003cc000

def z443 : W := mkw 0x0f6ce01200000000 0x00f6ce0120000000 0xeffff03f00000007 0xfeffff03f0000000

def z444 : W := mkw 0x4944848020000000 0x0494484802000000 0x004080c030000000 0x0004080c03000000

def z445 : W := mkw 0x10830b28c83131a8 0x810830b28c83131a 0xd1870f20c033338f 0x2d1870f20c033338

def z446 : W := mkw 0x0200648000000000 0x0020064800000000 0x30007fc000000004 0x030007fc00000000

def z447 : W := mkw 0x109109244c3331bc 0x8109109244c3331b 0x2030403c0c3333fe 0x72030403c0c3333f

def z448 : W := mkw 0x000018615215578a 0x4000018615215578 0x104038c0023fff8d 0xa104038c0023fff8

def z449 : W := mkw 0x2ffdf8775fffffdf 0x42ffdf8775fffffd 0xfffff8ffffffffff 0xffffff8fffffffff

def z450 : W := mkw 0x09c5800009282800 0x009c580000928280 0x8187000000000000 0x0818700000000000

def z451 : W := mkw 0x000010210201428a 0x0000010210201428 0x4048b023023fff8f 0xa4048b023023fff8

def z452 : W := mkw 0x062a621a80000000 0x0062a621a8000000 0xffbf7f3fc0000007 0xfffbf7f3fc000000

def z453 : W := mkw 0x4f6ce49220000000 0x04f6ce4922000000 0xbfc8ffc330000005 0xebfc8ffc33000000

def z454 : W := mkw 0x243800370483c09f 0x0243800370483c09 0x0e38003f0fc3c00a 0xf0e38003f0fc3c00

def z455 : W := mkw 0x0200784002540340 0x0020078400254034 0x3e4078c00ffc03fd 0xe3e4078c00ffc03f

def z456 : W := mkw 0x10020b2cc01111bc 0x810020b2cc01111b 0x70004f3cc03333ff 0x270004f3cc03333f

def z457 : W := mkw 0x2638787706d7c3df 0x02638787706d7c3d 0x3e7878ff0fffc3ff 0xf3e7878ff0fffc3f

def z458 : W := mkw 0x02007021024142ca 0x002007021024142c 0x2e0870230fc3c3fe 0xe2e0870230fc3c3f

def z459 : W := mkw 0x0000000001888800 0x0000000000188880 0x0000000003cccc00 0x00000000003cccc0

def z460 : W := mkw 0x1093022ccc23309c 0x81093022ccc23309 0xc1b7003ccc33300b 0x7c1b7003ccc33300

def z461 : W := mkw 0x0000082040111188 0x0000008204011118 0x5048b8e3f033338f 0xa5048b8e3f033338

def z462 : W := mkw 0x0000086050151588 0x4000008605015158 0x504088e0f03f3f8f 0x2504088e0f03f3f8

def z463 : W := mkw 0x89c01de15b3d57aa 0x489c01de15b3d57a 0xd1c8bfe3f23fff8f 0xad1c8bfe3f23fff8

def z464 : W := mkw 0xcfeeefdaa93c0120 0x0cfeeefdaa93c012 0xfffffffff03c0007 0xffffffffff03c000

def z465 : W := mkw 0x0000084050141500 0x4000008405014150 0x100008c0f0000000 0x0100008c0f000000

def z466 : W := mkw 0x8bc07de04b7d13e8 0x08bc07de04b7d13e 0xffc07fe0cfff33ff 0xeffc07fe0cfff33f

def z467 : W := mkw 0x0bc070000b680240 0x00bc070000b68024 0xafc070000ffc03fd 0xeafc070000ffc03f

def z468 : W := mkw 0x4d6e8688a0000000 0x04d6e8688a000000 0xdfff8fc0f0000003 0xfdfff8fc0f000000

def z469 : W := mkw 0x363b723fc6c3f2df 0x8363b723fc6c3f2d 0x6e3f703fcfc3f3fe 0xf6e3f703fcfc3f3f

def z470 : W := mkw 0x0000100002400240 0x0000010000240024 0x000000000fc003f8 0x0000000000fc003f

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400000023c0009 0xa00400000023c000

def z472 : W := mkw 0x04b900000ca2a000 0x004b900000ca2a00 0xcfbf00000ff3f00b 0xfcfbf00000ff3f00

def z473 : W := mkw 0x0200700002400240 0x0020070000240024 0x0e00300003c00000 0x80e00300003c0000

def z474 : W := mkw 0x59c78f88e8303120 0x859c78f88e830312 0xd1c78fc0f0303001 0x0d1c78fc0f030300

def z475 : W := mkw 0xaff865960dea8075 0x0aff865960dea807 0xafb0471c0dc00070 0x5afb0471c0dc0007

def z476 : W := mkw 0x8080010009680060 0x0808001000968006 0x000000000dc00070 0x0000000000dc0007

def z477 : W := mkw 0x10130a2cc413319c 0x810130a2cc413319 0x5037083cc033338f 0x35037083cc033338

def z478 : W := mkw 0x4f6efefbf215578a 0x44f6efefbf215578 0xfffffffff0000387 0xffffffffff000038

def z479 : W := mkw 0x09d100000daaa800 0x009d100000daaa80 0x8fc000000ffffc09 0xe8fc000000ffffc0

def z480 : W := mkw 0x09c0000009280000 0x009c000000928000 0x81c00000003c0001 0x081c00000003c000

def z481 : W := mkw 0x52936fbeec3331bc 0x852936fbeec3331b 0xf1b77ffffc3333ff 0x7f1b77ffffc3333f

def z482 : W := mkw 0x8ffde5800deaa860 0x08ffde5800deaa86 0xafb747000dc00070 0x5afb747000dc0007

def z483 : W := mkw 0x4ffffefbffbfff8a 0x44ffffefbffbfff8 0xffffffffffffff8f 0xfffffffffffffff8

def z484 : W := mkw 0x000018615215578a 0x4000018615215578 0x40488000023fff8b 0xa40488000023fff8

def z485 : W := mkw 0x0dfd88405dbebd00 0x40dfd88405dbebd0 0xdfff88c0fffffc0b 0xfdfff88c0fffffc0

def z486 : W := mkw 0x001000240403009c 0x0001000240403009 0x000000000c0303f8 0x0000000000c0303f

def z487 : W := mkw 0x000018615215578a 0x4000018615215578 0x1048b8e3f20ccf84 0x81048b8e3f20ccf8

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e0000000fc00008 0xe0e0000000fc0000

def z489 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xaffff7df30000000 0xdaffff7df3000000

def z490 : W := mkw 0x8bd17dc00ffeab60 0x08bd17dc00ffeab6 0xbfc07fc00ffffffd 0xebfc07fc00ffffff

def z491 : W := mkw 0x0000082040111188 0x0000008204011118 0x0000000000333388 0x0000000000033338

def z492 : W := mkw 0x2638707716c7c6df 0x42638707716c7c6d 0x2e78f0ff3fcfcffe 0xf2e78f0ff3fcfcff

def z493 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcff780000dfc3c01 0x5cff780000dfc3c0

def z494 : W := mkw 0x808019400b7c0360 0x0808019400b7c036 0x104038c00ffc03fd 0xa104038c00ffc03f

def z495 : W := mkw 0x2638701306c2c243 0x02638701306c2c24 0x0e3830030fc3c00a 0xf0e3830030fc3c00

def z496 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xb1c07fc0003c03f5 0x0b1c07fc0003c03f

def z497 : W := mkw 0x40020688a0000000 0x040020688a000000 0x10000fc0f0000000 0x010000fc0f000000

def z498 : W := mkw 0x001000240403009c 0x0001000240403009 0x0030003c00030002 0x10030003c0003000

def z499 : W := mkw 0x000018615215578a 0x4000018615215578 0x0048b0c3323fff88 0x80048b0c3323fff8

def z500 : W := mkw 0x000018615215578a 0x4000018615215578 0x5040b8e3f03c3f85 0x05040b8e3f03c3f8

def z501 : W := mkw 0x0000184052141700 0x4000018405214170 0x5040b8c0f23c3f8d 0xa5040b8c0f23c3f8

def z502 : W := mkw 0xcfffffdaaffeab60 0x0cfffffdaaffeab6 0xffffffffffffffff 0xffffffffffffffff

def z503 : W := mkw 0x36b979374ef3f3ff 0x836b979374ef3f3f 0x2e38703f0ff3f3fe 0xf2e38703f0ff3f3f

def z504 : W := mkw 0x40068208a0000000 0x040068208a000000 0x40078000f0000000 0x040078000f000000

def z505 : W := mkw 0x09d100000d2a2000 0x009d100000d2a200 0xcff700000fff300b 0xfcff700000fff300

def z506 : W := mkw 0x443f821aa482a800 0x0443f821aa482a80 0x403f803ff003fc02 0x1403f803ff003fc0

def z507 : W := mkw 0x2628787352d5d7cb 0x42628787352d5d7c 0x5e48b8e3f3ffff8f 0xa5e48b8e3f3ffff8

def z508 : W := mkw 0x000018615215578a 0x4000018615215578 0x100838e3f203c38e 0xa100838e3f203c38

def z509 : W := mkw 0x2438102506c3c2df 0x02438102506c3c2d 0x0e3800000fc3c3fa 0xf0e3800000fc3c3f

def z510 : W := mkw 0x442c801220000000 0x0442c80122000000 0x0008800330000000 0x0000880033000000

def z511 : W := mkw 0x10930b2ddc3375be 0xc10930b2ddc3375b 0xf1bfcf3ffc33ffff 0x7f1bfcf3ffc33fff

def z512 : W := mkw 0x0000104002040200 0x0000010400204020 0x004030c0020c0000 0x8004030c0020c000

def z513 : W := mkw 0x10931b6dde3777be 0xc10931b6dde3777b 0xf1b74f3cce3fffff 0x7f1b74f3cce3ffff

def z514 : W := mkw 0x7fffffbfeef3f3ff 0x87fffffbfeef3f3f 0xfffffffffff3f3ff 0xffffffffffff3f3f

def z515 : W := mkw 0x80800940093c0120 0x080800940093c012 0x00000000003c0000 0x000000000003c000

def z516 : W := mkw 0x12937b2cce7333fc 0x812937b2cce7333f 0xffb77f3ccff333ff 0xfffb77f3ccff333f

def z517 : W := mkw 0x1dff830c8daaa834 0x81dff830c8daaa83 0xefffc71c0ffffc7b 0xfefffc71c0ffffc7

def z518 : W := mkw 0x000018615215578a 0x4000018615215578 0x500038e3f033338f 0x2500038e3f033338

def z519 : W := mkw 0x1bd36faccc3331bc 0x81bd36faccc3331b 0xfff77ffccc3333ff 0xffff77ffccc3333f

def z520 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2038703f0003c3f6 0x12038703f0003c3f

def z521 : W := mkw 0x000018615215578a 0x4000018615215578 0x504088c0f23fff89 0x0504088c0f23fff8

def z522 : W := mkw 0x808019615b7d57ea 0x4808019615b7d57e 0x5048b8e3ffffffff 0xa5048b8e3fffffff

def z523 : W := mkw 0x3ffffb3fcffbfbff 0x83ffffb3fcffbfbf 0xffffff3fcfffffff 0xfffffff3fcffffff

def z524 : W := mkw 0x8fecfdc00bfc8b60 0x08fecfdc00bfc8b6 0xbfc8ffc00ffccffd 0xebfc8ffc00ffccff

def z525 : W := mkw 0x9bd17de44f7f33fc 0x89bd17de44f7f33f 0xbfc07fc00fff33fd 0xebfc07fc00fff33f

def z526 : W := mkw 0x92027fecc25513fc 0x892027fecc25513f 0x30007ffcc00003f4 0x030007ffcc00003f

def z527 : W := mkw 0x04bd80000ca2a800 0x004bd80000ca2a80 0xc1bf80000c33fc0b 0x7c1bf80000c33fc0

def z528 : W := mkw 0x0628601200000000 0x0062860120000000 0x2e30401c00000000 0x52e30401c0000000

def z529 : W := mkw 0x809119400ffeab60 0x0809119400ffeab6 0x000000000ffffff8 0x0000000000ffffff

def z530 : W := mkw 0x0d6c800000000000 0x00d6c80000000000 0xcfff8000023ffc0b 0xfcfff8000023ffc0

def z531 : W := mkw 0x0005800000002800 0x0000580000000280 0x4007800000003c00 0x04007800000003c0

def z532 : W := mkw 0xdffffffeef7f33fc 0x8dffffffeef7f33f 0xffffffffffff33ff 0xfffffffffffff33f

def z533 : W := mkw 0x0d6c800001888800 0x00d6c80000188880 0xcfff800003cccc03 0xfcfff800003cccc0

def z534 : W := mkw 0x0ffdf0000feaaa40 0x00ffdf0000feaaa4 0xeffff0000fffffff 0xfeffff0000ffffff

def z535 : W := mkw 0x09c598615b3d7f8a 0x409c598615b3d7f8 0xd1cfb8e3f23fff8f 0xad1cfb8e3f23fff8

def z536 : W := mkw 0x92937fecce7733fc 0x892937fecce7733f 0xf1b77ffccc3333ff 0x7f1b77ffccc3333f

def z537 : W := mkw 0x10021b6dd21557be 0xc10021b6dd21557b 0x30007ffff00003f4 0x030007ffff00003f

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1b7000000000003 0x7c1b700000000000

def z539 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xd1870f00cc3333f9 0x0d1870f00cc3333f

def z540 : W := mkw 0x1dff8b2ccdbbb9bc 0x81dff8b2ccdbbb9b 0xffb74f3ccdf333ff 0x7ffb74f3ccdf333f

def z541 : W := mkw 0x9bd37fcc8f7e2374 0x89bd37fcc8f7e237 0xbff77fdc0ffc03fd 0xfbff77fdc0ffc03f

def z542 : W := mkw 0x4f6cf4d332044602 0x44f6cf4d33204460 0x0e48b0c3320ccc00 0x80e48b0c3320ccc0

def z543 : W := mkw 0xcf6effdaa2540360 0x0cf6effdaa254036 0xfffffffff00003f7 0xffffffffff00003f

def z544 : W := mkw 0xaf6874d303ccc243 0x0af6874d303ccc24 0x0e4830c303ccc000 0x80e4830c303ccc00

def z545 : W := mkw 0x2638783746d3d3df 0x02638783746d3d3d 0x7e38783fcff3f3ff 0xf7e38783fcff3f3f

def z546 : W := mkw 0x2200701302404243 0x0220070130240424 0x0000300300000000 0x0000030030000000

def z547 : W := mkw 0x000008215011558a 0x4000008215011558 0x50088823f033ff8f 0x250088823f033ff8

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0x104038c000000005 0xa104038c00000000

def z549 : W := mkw 0x009118615e37778a 0x4009118615e37778 0xd1ffb8e3fe3fff8f 0xfd1ffb8e3fe3fff8

def z550 : W := mkw 0x99d30feccd3f31bc 0x899d30feccd3f31b 0xf1f74ffccc3f33ff 0x7f1f74ffccc3f33f

def z551 : W := mkw 0x2628601200c08041 0x02628601200c0804 0x0e00000001c00000 0x00e00000001c0000

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0x40408000003c3c01 0x040408000003c3c0

def z553 : W := mkw 0x19d78b2ccd3b39bc 0x819d78b2ccd3b39b 0xf1f7cf3ccc3f3fff 0x7f1f7cf3ccc3f3ff

def z554 : W := mkw 0x80001040034c0240 0x080001040034c024 0x0000000003cc0000 0x00000000003cc000

def z555 : W := mkw 0xabd07de50fffc3ff 0x0abd07de50fffc3f 0xbfc07fc00fffc3fd 0xebfc07fc00fffc3f

def z556 : W := mkw 0x6f7ee6bfa483c09f 0x06f7ee6bfa483c09 0xfffffffff003c007 0xffffffffff003c00

def z557 : W := mkw 0x52026fbee01111bc 0x852026fbee01111b 0x30007ffff00003f4 0x030007ffff00003f

def z558 : W := mkw 0x442e9a7bf215578a 0x4442e9a7bf215578 0x507fb8fff23fff8f 0xb507fb8fff23fff8

def z559 : W := mkw 0x82007dc002540360 0x082007dc00254036 0x30407fc0023c03fd 0xa30407fc0023c03f

def z560 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x8fb700000ffffc08 0x58fb700000ffffc0

def z561 : W := mkw 0x20001025024142df 0x020001025024142d 0x00000000000003f0 0x000000000000003f

def z562 : W := mkw 0x09d580000d2a2800 0x009d580000d2a280 0xc1f780000c3f3c0b 0x7c1f780000c3f3c0

def z563 : W := mkw 0x6f6cf49322c0c243 0x06f6cf49322c0c24 0x0e48b0c333c0c000 0x80e48b0c333c0c00

def z564 : W := mkw 0x4f6eeedaf0141500 0x44f6eeedaf014150 0xfffffffff03c3c07 0xffffffffff03c3c0

def z565 : W := mkw 0x0ffde4800daaa800 0x00ffde4800daaa80 0xffffffc00ffffc0f 0xfffffffc00ffffc0

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0x000800000203c00a 0xa000800000203c00

def z567 : W := mkw 0x000000210001408a 0x0000000210001408 0x000800230003c002 0x0000800230003c00

def z568 : W := mkw 0x243d80370483e89f 0x0243d80370483e89 0x403f803f0003fc02 0x1403f803f0003fc0

def z569 : W := mkw 0x2000100102c0c243 0x02000100102c0c24 0x0000000003c0c000 0x00000000003c0c00

def z570 : W := mkw 0x89c00dc0593c1520 0x489c00dc0593c152 0xd1c08fc0f03c3c01 0x0d1c08fc0f03c3c0

def z571 : W := mkw 0x808019615b7d57ea 0x4808019615b7d57e 0x000000000ffffff8 0x0000000000ffffff

def z572 : W := mkw 0x0f6ce48000000000 0x00f6ce4800000000 0xffffffc000000007 0xfffffffc00000000

def z573 : W := mkw 0x0000104112044602 0x4000010411204460 0x5048b8e3f20ccc07 0xa5048b8e3f20ccc0

def z574 : W := mkw 0x8b4074c0034c0240 0x08b4074c0034c024 0xbfc07fc003cc0005 0xebfc07fc003cc000

def z575 : W := mkw 0x8bc07de15b7d57ea 0x48bc07de15b7d57e 0xbfc07fe3fffc03fd 0xebfc07fe3fffc03f

def z576 : W := mkw 0x26b970370ee3e2df 0x026b970370ee3e2d 0xefbf703f0ff3f3ff 0xfefbf703f0ff3f3f

def z577 : W := mkw 0x442e821aa0000000 0x0442e821aa000000 0xf1bfcf3ff0000007 0x7f1bfcf3ff000000

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000000033300b 0x2400000000033300

def z579 : W := mkw 0x0dfd90411faeee02 0x40dfd90411faeee0 0xcfffb0c33ffffc0b 0xfcfffb0c33ffffc0

def z580 : W := mkw 0x2638787756d7d7df 0x42638787756d7d7d 0x2e38703f0ffffffe 0xf2e38703f0ffffff

def z581 : W := mkw 0x0000104112044602 0x4000010411204460 0x4048b0c3323ffc0b 0xa4048b0c3323ffc0

def z582 : W := mkw 0x009302088c222000 0x0009302088c22200 0xf1b74f3ccc33300f 0x7f1b74f3ccc33300

def z583 : W := mkw 0x0002020880000000 0x0000202088000000 0x4037003cc0000002 0x14037003cc000000

def z584 : W := mkw 0xcf6ef6daa34c0240 0x0cf6ef6daa34c024 0xfffffffff3cc0007 0xffffffffff3cc000

def z585 : W := mkw 0x0638601204828000 0x0063860120482800 0x2e38703f0fc3c00e 0xf2e38703f0fc3c00

def z586 : W := mkw 0x16bb6b3ecc3331bc 0x816bb6b3ecc3331b 0xffbf7f3fcc3333ff 0xfffbf7f3fcc3333f

def z587 : W := mkw 0x4f6ef6dbb2044602 0x44f6ef6dbb204460 0xfffffffff20ccc07 0xffffffffff20ccc0

def z588 : W := mkw 0x820074c002440240 0x0820074c00244024 0x000030c000000000 0x0000030c00000000

def z589 : W := mkw 0x043d98615697ff8a 0x4043d98615697ff8 0x507fb8e3f23fff8f 0xb507fb8e3f23fff8

def z590 : W := mkw 0x32027b3fc25153ff 0x832027b3fc25153f 0x30007f3fc00003f4 0x030007f3fc00003f

def z591 : W := mkw 0x6f7ef6bfa6c3c2df 0x06f7ef6bfa6c3c2d 0xafbf773f0fc3c3fe 0xfafbf773f0fc3c3f

def z592 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfff7cfdcf0000001 0x5fff7cfdcf000000

def z593 : W := mkw 0x10020b08c0101120 0x810020b08c010112 0x10000f00c0000000 0x010000f00c000000

def z594 : W := mkw 0x82007de1525557ea 0x482007de1525557e 0x7048ffe3f23fffff 0xa7048ffe3f23ffff

def z595 : W := mkw 0x36bb631e8ce2a075 0x836bb631e8ce2a07 0xafb7471c0dc00070 0x5afb7471c0dc0007

def z596 : W := mkw 0xcfecfdd22b7c0360 0x0cfecfdd22b7c036 0xbfc8ffc33ffc03fd 0xebfc8ffc33ffc03f

def z597 : W := mkw 0x10931b2dce3373be 0x810931b2dce3373b 0xf1bf7f3fce33f3ff 0xff1bf7f3fce33f3f

def z598 : W := mkw 0x4fffe69aadaaa800 0x04fffe69aadaaa80 0xefffc71c0ffffc0b 0xfefffc71c0ffffc0

def z599 : W := mkw 0x009100000daaa800 0x0009100000daaa80 0x404880000ffffc0b 0xa404880000ffffc0

def z600 : W := mkw 0x0940048000000000 0x0094004800000000 0x91c00fc000000001 0x091c00fc00000000

def z601 : W := mkw 0x6ffff6bfafebeadf 0x06ffff6bfafebead 0xffffffffffffffff 0xffffffffffffffff

def z602 : W := mkw 0x89c00dc0093c0120 0x089c00dc0093c012 0x9fc00fc00ffc0009 0xe9fc00fc00ffc000

def z603 : W := mkw 0x000018615215578a 0x4000018615215578 0x5008b8e3f003ff86 0x05008b8e3f003ff8

def z604 : W := mkw 0x2438103706c3c2df 0x02438103706c3c2d 0x0038003f0fc3c3fa 0x10038003f0fc3c3f

def z605 : W := mkw 0x2dfd90250febeadf 0x02dfd90250febead 0xcfff80000ffffffb 0xfcfff80000ffffff

def z606 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xafbf773f00000006 0xfafbf773f0000000

def z607 : W := mkw 0x0dec800009a88800 0x00dec800009a8880 0x8fc880000ffccc09 0xe8fc880000ffccc0

def z608 : W := mkw 0x009108204c333188 0x0009108204c33318 0xd1b70820cc33338f 0x7d1b70820cc33338

def z609 : W := mkw 0x09c0000009280000 0x009c000000928000 0x8f8000000dc00000 0x48f8000000dc0000

def z610 : W := mkw 0x0000100102004202 0x0000010010200420 0x000830030200c000 0x8000830030200c00

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z612 : W := mkw 0x0000104112044602 0x4000010411204460 0x00000000020ccc00 0x000000000020ccc0

def z613 : W := mkw 0x00800920483111a8 0x000800920483111a 0xf1804f20cc3333ff 0x6f1804f20cc3333f

def z614 : W := mkw 0x0dfd80215dabfc8a 0x40dfd80215dabfc8 0xcfff8023fffffc0b 0xfcfff8023fffffc0

def z615 : W := mkw 0x09d580000daaa800 0x009d580000daaa80 0xc1c780000ffffc09 0x0c1c780000ffffc0

def z616 : W := mkw 0x0b407cc002140300 0x00b407cc00214030 0xbfc07fc0023c038d 0xebfc07fc0023c038

def z617 : W := mkw 0x0dfd98615fbfff8a 0x40dfd98615fbfff8 0xcfff80000fffff8b 0xfcfff80000fffff8

def z618 : W := mkw 0x442e821aa0000000 0x0442e821aa000000 0x0037001c00000000 0x10037001c0000000

def z619 : W := mkw 0xaff875b70febc2ff 0x0aff875b70febc2f 0xafb8773f0fc3c3fe 0xfafb8773f0fc3c3f

def z620 : W := mkw 0x009100000c222000 0x0009100000c22200 0x81b700000c000000 0x581b700000c00000

def z621 : W := mkw 0x42027efbf215578a 0x442027efbf215578 0x30007ffff0000384 0x030007ffff000038

def z622 : W := mkw 0x0d6c800000000000 0x00d6c80000000000 0x0e48800000000000 0x80e4880000000000

def z623 : W := mkw 0xafe87dd30bfcc363 0x0afe87dd30bfcc36 0xbfc87fc30ffcc3fd 0xebfc87fc30ffcc3f

def z624 : W := mkw 0xa6b879770fffc3ff 0x0a6b879770fffc3f 0x2e38703f0fffc3fe 0xf2e38703f0fffc3f

def z625 : W := mkw 0x0080010008200020 0x0008001000820002 0xa18047000c000070 0x4a18047000c00007

def z626 : W := mkw 0x10830b2cc83131bc 0x810830b2cc83131b 0xf1874f3cc03033f5 0x0f1874f3cc03033f

def z627 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x0e0830030fc3c3f8 0x80e0830030fc3c3f

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x40088023f0000002 0x040088023f000000

def z629 : W := mkw 0x442e821aa0000000 0x0442e821aa000000 0x507fb8fff0000007 0xb507fb8fff000000

def z630 : W := mkw 0x2f7cf03707cbcadf 0x02f7cf03707cbcad 0x2e78f03f0fcfcffe 0xf2e78f03f0fcfcff

def z631 : W := mkw 0x49c78688a9282800 0x049c78688a928280 0xd1c78fc0f03c3c01 0x0d1c78fc0f03c3c0

def z632 : W := mkw 0x1081090048303120 0x8108109004830312 0x0000000000303000 0x0000000000030300

def z633 : W := mkw 0x062878735215578a 0x4062878735215578 0x7e78f8fff23fff8f 0xf7e78f8fff23fff8

def z634 : W := mkw 0x0dec800009280000 0x00dec80000928000 0xcfff80000ffc000b 0xfcfff80000ffc000

def z635 : W := mkw 0x8b4074c1134c4642 0x48b4074c1134c464 0x0e48b0c333cccc00 0x80e48b0c333cccc0

def z636 : W := mkw 0x9fffffeccfffbbfc 0x89fffffeccfffbbf 0xfffffffccfffffff 0xffffffffccffffff

def z637 : W := mkw 0x0200601200000000 0x0020060120000000 0x2000703f00000004 0x02000703f0000000

def z638 : W := mkw 0xa6387df706d7c3ff 0x0a6387df706d7c3f 0x3e387fff0fc3c3fe 0xf3e387fff0fc3c3f

def z639 : W := mkw 0x2ffdf0130feaea43 0x02ffdf0130feaea4 0xcfffb0030ffffc0b 0xfcfffb0030ffffc0

def z640 : W := mkw 0xaffdfdf70fffebff 0x0affdfdf70fffebf 0xffffffff0fffffff 0xfffffffff0ffffff

def z641 : W := mkw 0x309119254ef3f3ff 0x8309119254ef3f3f 0x000000000ff3f3f8 0x0000000000ff3f3f

def z642 : W := mkw 0x0d6c800001888800 0x00d6c80000188880 0x0e00000001c00000 0x00e00000001c0000

def z643 : W := mkw 0x000000215001548a 0x4000000215001548 0x40488023f23ffc0b 0xa40488023f23ffc0

def z644 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x8fff80000fcccc00 0xd8fff80000fcccc0

def z645 : W := mkw 0x36bb6b3eccf3b1fd 0x836bb6b3eccf3b1f 0xffb74f3ccdf333ff 0x7ffb74f3ccdf333f

def z646 : W := mkw 0xabc07df70b7d43ff 0x0abc07df70b7d43f 0xbfc07fff0ffc03fd 0xebfc07fff0ffc03f

def z647 : W := mkw 0x4f6ce49220000000 0x04f6ce4922000000 0x0e00000000000000 0x00e0000000000000

def z648 : W := mkw 0x04b900000daaa800 0x004b900000daaa80 0x0e3800000ffffc0a 0xf0e3800000ffffc0

def z649 : W := mkw 0x59d78facec3331bc 0x859d78facec3331b 0xf1f7cffcfc3333ff 0x7f1f7cffcfc3333f

def z650 : W := mkw 0x543f823ee403309c 0x8543f823ee403309 0x403f803ff0033002 0x1403f803ff003300

def z651 : W := mkw 0x0b42668880000000 0x00b4266888000000 0xfff77ffcc0000007 0xffff77ffcc000000

def z652 : W := mkw 0x0200600000000000 0x0020060000000000 0x2e00700000000004 0xe2e0070000000000

def z653 : W := mkw 0x043d80000482a800 0x0043d80000482a80 0x0037000000000000 0x1003700000000000

def z654 : W := mkw 0x0000084000140100 0x0000008400014010 0x104008c0003c0001 0x0104008c0003c000

def z655 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xefbfc73ff0000002 0x5efbfc73ff000000

def z656 : W := mkw 0x001018655617579e 0x4001018655617579 0x7078f8fffe3fffff 0xf7078f8fffe3ffff

def z657 : W := mkw 0xcbc6ffc8ab7c0360 0x0cbc6ffc8ab7c036 0xffc7ffc0fffc03fd 0xeffc7ffc0fffc03f

def z658 : W := mkw 0x2dfd80370dabe89f 0x02dfd80370dabe89 0xcfff803f0ffffc0b 0xfcfff803f0ffffc0

def z659 : W := mkw 0x2ffde0160deaa855 0x02ffde0160deaa85 0xafb7401c0dc00070 0x5afb7401c0dc0007

def z660 : W := mkw 0x0ded800009282800 0x00ded80000928280 0xcfff8000003c3c03 0xfcfff8000003c3c0

def z661 : W := mkw 0x6f7ee69ea4c28055 0x06f7ee69ea4c2805 0xfffffffffdc00077 0xffffffffffdc0007

def z662 : W := mkw 0x4dff821aadaaa800 0x04dff821aadaaa80 0xcfff803ffffffc0b 0xfcfff803ffffffc0

def z663 : W := mkw 0x0000002000010088 0x0000000200001008 0x000000200003038e 0x2000000200003038

def z664 : W := mkw 0x000010611205468a 0x4000010611205468 0x0048b0e3320fcf8e 0xa0048b0e3320fcf8

def z665 : W := mkw 0x4f6ce49220000000 0x04f6ce4922000000 0x5e48b8e3f0000007 0xa5e48b8e3f000000

def z666 : W := mkw 0x5f7fe6bee403309c 0x85f7fe6bee403309 0xfffffffff0033007 0xffffffffff003300

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x400880000003fc02 0x0400880000003fc0

def z668 : W := mkw 0x49468688a0000000 0x049468688a000000 0xf1f7cffcf0000007 0x7f1f7cffcf000000

def z669 : W := mkw 0x8bc06dc0097c0160 0x08bc06dc0097c016 0xbfc04fc00dfc0071 0x4bfc04fc00dfc007

def z670 : W := mkw 0xcbc27fdaab7c0360 0x0cbc27fdaab7c036 0xbfc07ffffffc03fd 0xebfc07ffffffc03f

def z671 : W := mkw 0x209110250febeadf 0x0209110250febead 0x000000000ffffff8 0x0000000000ffffff

def z672 : W := mkw 0x26287037024142df 0x026287037024142d 0x2e38703f000003f6 0xf2e38703f000003f

def z673 : W := mkw 0x0080000009280000 0x0008000000928000 0x000000000ffc0008 0x0000000000ffc000

def z674 : W := mkw 0x4f7ee6bea403009c 0x04f7ee6bea403009 0xfffffffffc0303ff 0xffffffffffc0303f

def z675 : W := mkw 0x2010186556d7d7df 0x42010186556d7d7d 0x5048b8e3ffffffff 0xa5048b8e3fffffff

def z676 : W := mkw 0x2628701302c0c243 0x02628701302c0c24 0x2e38703f03c0c006 0xf2e38703f03c0c00

def z677 : W := mkw 0x0081000008202000 0x0008100000820200 0xc187000000303001 0x0c18700000030300

def z678 : W := mkw 0x8b40648001480040 0x08b4064800148004 0x0e00000001c00000 0x00e00000001c0000

def z679 : W := mkw 0xaff87dd60ffe8375 0x0aff87dd60ffe837 0xbff07fdc0ffc03fd 0xfbff07fdc0ffc03f

def z680 : W := mkw 0x009100240c23209c 0x0009100240c23209 0xe1b7403c0c3333ff 0x7e1b7403c0c3333f

def z681 : W := mkw 0x8bc075c00b6c0260 0x08bc075c00b6c026 0xafc077c00fcc0070 0xcafc077c00fcc007

def z682 : W := mkw 0x0200600000400040 0x0020060000040004 0x2e0040000dc00070 0x42e0040000dc0007

def z683 : W := mkw 0xcfeeffdaab7c0360 0x0cfeeffdaab7c036 0xbff77fdc0ffc03fd 0xfbff77fdc0ffc03f

def z684 : W := mkw 0x000010210201428a 0x0000010210201428 0x5048b8e3f203c38f 0xa5048b8e3f203c38

def z685 : W := mkw 0x8ffdfdc00ffeab60 0x08ffdfdc00ffeab6 0xbff77fc00ffc03fd 0xfbff77fc00ffc03f

def z686 : W := mkw 0x0000002040011088 0x0000000204001108 0x40000020c0033002 0x040000020c003300

def z687 : W := mkw 0x000010615205568a 0x4000010615205568 0x4048b0e3f20ffc02 0x84048b0e3f20ffc0

def z688 : W := mkw 0x0000082040111188 0x0000008204011118 0x50488820c23fff8f 0xa50488820c23fff8

def z689 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0x9fc03fc003fc0001 0x89fc03fc003fc000

def z690 : W := mkw 0x49469ee9f215578a 0x449469ee9f215578 0xd1cfbfe3f23fff8f 0xad1cfbfe3f23fff8

def z691 : W := mkw 0x90931b6ccf7f33fc 0x890931b6ccf7f33f 0xf1b74f3ccfff33ff 0x7f1b74f3ccfff33f

def z692 : W := mkw 0x8b4074c0034c0240 0x08b4074c0034c024 0x2e4070c00fcc03fc 0xe2e4070c00fcc03f

def z693 : W := mkw 0x0000100002000200 0x0000010000200020 0x000030000200038c 0xa000030000200038

def z694 : W := mkw 0x000018615215578a 0x4000018615215578 0x5048b8e3f0000387 0xa5048b8e3f000038

def z695 : W := mkw 0x808019400b7c0360 0x0808019400b7c036 0xb1804f000ffc03fd 0x6b1804f000ffc03f

def z696 : W := mkw 0x000018610215438a 0x0000018610215438 0x104838e3023fc38f 0xa104838e3023fc38

def z697 : W := mkw 0x2f7874b706c3c2df 0x02f7874b706c3c2d 0xbff87fff0fc3c3ff 0xfbff87fff0fc3c3f

def z698 : W := mkw 0x8b407cc0035c0340 0x08b407cc0035c034 0x1e4038c003fc038d 0xa1e4038c003fc038

def z699 : W := mkw 0x0ded800009a8a800 0x00ded800009a8a80 0xcfcf800003fcfc01 0x8cfcf800003fcfc0

def z700 : W := mkw 0x1093032ccc2330bc 0x81093032ccc2330b 0xe1b7473ccc033072 0x5e1b7473ccc03307

def z701 : W := mkw 0x001008244413119c 0x0001008244413119 0x7030483ccc3333ff 0x77030483ccc3333f

def z702 : W := mkw 0x0000090000100120 0x0000009000010012 0x30004f00000003f4 0x030004f00000003f

def z703 : W := mkw 0x09c018615b3d578a 0x409c018615b3d578 0xdfc8b8e3ffffff8f 0xedfc8b8e3ffffff8

def z704 : W := mkw 0x6f7ee69ea4c28055 0x06f7ee69ea4c2805 0xafb7471c0dc00070 0x5afb7471c0dc0007

def z705 : W := mkw 0x2ffde0160deaa855 0x02ffde0160deaa85 0xefffc01c0ffffc7b 0xfefffc01c0ffffc7

def z706 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0x4e7fb0fff0000002 0x94e7fb0fff000000

def z707 : W := mkw 0x0280690008700160 0x0028069000870016 0xbf804f000df003fd 0x6bf804f000df003f

def z708 : W := mkw 0x0000082040111188 0x0000008204011118 0x5048b8e3f23fff8f 0xa5048b8e3f23fff8

def z709 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e30701c0fc3c3fc 0xf2e30701c0fc3c3f

def z710 : W := mkw 0xcf6cf4d2234c0240 0x0cf6cf4d2234c024 0x0e4030c003cc0000 0x80e4030c003cc000

def z711 : W := mkw 0x4f6efefbf215578a 0x44f6efefbf215578 0xafb7471c023fff88 0x5afb7471c023fff8

def z712 : W := mkw 0x8bc065a1596954ea 0x48bc065a1596954e 0xef88c723fdc3fc72 0x4ef88c723fdc3fc7

def z713 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e30401c0dc003f0 0x52e30401c0dc003f

def z714 : W := mkw 0xadf80df70dbfc1bf 0x0adf80df70dbfc1b 0x91f80fff003fc003 0x191f80fff003fc00

def z715 : W := mkw 0x243800370483c09f 0x0243800370483c09 0x2e38403f0fc3c3fe 0xf2e38403f0fc3c3f

def z716 : W := mkw 0x8bc075800b680260 0x08bc075800b68026 0xaf8047000fc003f8 0x4af8047000fc003f

def z717 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e38703f0dc3c3f6 0x52e38703f0dc3c3f

def z718 : W := mkw 0x0d7d8000058aa800 0x00d7d8000058aa80 0x4e7f800003fffc0b 0xb4e7f800003fffc0

def z719 : W := mkw 0x442e821aa0000000 0x0442e821aa000000 0xf1fffffff0000007 0xff1fffffff000000

def z720 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1f7cffcfc3333ff 0x7f1f7cffcfc3333f

def z721 : W := mkw 0x000008615015558a 0x4000008615015558 0x5048b8e3f03ffc07 0xa5048b8e3f03ffc0

def z722 : W := mkw 0x263df03756c3fedf 0x4263df03756c3fed 0x6e3ff03fffc3fffe 0xf6e3ff03fffc3fff

def z723 : W := mkw 0x8bc075800b680260 0x08bc075800b68026 0xaf8077000dc003f4 0x4af8077000dc003f

def z724 : W := mkw 0x36ab7b1bcaf0f363 0x836ab7b1bcaf0f36 0xdf8f3f03c3f0f001 0x8df8f3f03c3f0f00

def z725 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xaf8077000ffc03fc 0xeaf8077000ffc03f

def z726 : W := mkw 0x663874b726c3c2df 0x0663874b726c3c2d 0x2e3870ff3fc3c3fe 0xf2e3870ff3fc3c3f

def z727 : W := mkw 0x00930b088c322120 0x000930b088c32212 0xf1b74f3ccc3333ff 0x7f1b74f3ccc3333f

def z728 : W := mkw 0x09c5800009282800 0x009c580000928280 0xcfcf80000ffffc0b 0xecfcf80000ffffc0

def z729 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1f74f3cce3f33ff 0xff1f74f3cce3f33f

def z730 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffff23c000f 0xffffffffff23c000

def z731 : W := mkw 0x19c78b48d93c3d20 0xc19c78b48d93c3d2 0xd1c78fc0f03c3c01 0x0d1c78fc0f03c3c0

def z732 : W := mkw 0x4f6ee69aa1080000 0x04f6ee69aa108000 0xfffffffff3cc0007 0xffffffffff3cc000

def z733 : W := mkw 0x8bc075800b680260 0x08bc075800b68026 0xbfc07fc00fc003fd 0xebfc07fc00fc003f

def z734 : W := mkw 0x82007dc002540360 0x082007dc00254036 0x3e007fc00dc003f4 0x43e007fc00dc003f

def z735 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1fffffffe3fffff 0xff1fffffffe3ffff

def z736 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e30703f0fc3c3fc 0x52e30703f0fc3c3f

def z737 : W := mkw 0x10930b2c8c3321bc 0x810930b2c8c3321b 0xb1b74f3c0c3303ff 0x7b1b74f3c0c3303f

def z738 : W := mkw 0x1093032c8c2320bc 0x81093032c8c2320b 0xa1b7473c0c0003f4 0x5a1b7473c0c0003f

def z739 : W := mkw 0x828079400b7c0360 0x0828079400b7c036 0xbf807f000ffc03fd 0xebf807f000ffc03f

def z740 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xafc047000ffc03f9 0xeafc047000ffc03f

def z741 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x0e38303f0fc3c3fa 0x90e38303f0fc3c3f

def z742 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbf807fc00df003fd 0x6bf807fc00df003f

def z743 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffff03c3c07 0xffffffffff03c3c0

def z744 : W := mkw 0x263df03706c3eadf 0x0263df03706c3ead 0x2e3f703f0fc3c3fe 0xf2e3f703f0fc3c3f

def z745 : W := mkw 0x462a669aa0000000 0x0462a669aa000000 0xffbf7ffff0000007 0xfffbf7ffff000000

def z746 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0x9fc03fc00ffc03f9 0x89fc03fc00ffc03f

def z747 : W := mkw 0x8dfd85800daaa820 0x08dfd85800daaa82 0xcfff87000ffffc0b 0xfcfff87000ffffc0

def z748 : W := mkw 0x2638685654d69555 0x42638685654d6955 0x7e70c8dcfdfc3c71 0x57e70c8dcfdfc3c7

def z749 : W := mkw 0x0dfd98615fbfff8a 0x40dfd98615fbfff8 0x9fb738e3fdc00384 0x59fb738e3fdc0038

def z750 : W := mkw 0x10930b2ddc3375be 0xc10930b2ddc3375b 0xf1b74f3ccc33ffff 0x7f1b74f3ccc33fff

def z751 : W := mkw 0x22007037024142df 0x022007037024142d 0x2e08703f0fc3c3fe 0xe2e08703f0fc3c3f

def z752 : W := mkw 0x99c78fc8c93c3920 0x899c78fc8c93c392 0xd1c78fc0c03c3c01 0x0d1c78fc0c03c3c0

def z753 : W := mkw 0x8bc06d8009780160 0x08bc06d800978016 0xbf804f000dc003f4 0x4bf804f000dc003f

def z754 : W := mkw 0x4293669aadaaa800 0x04293669aadaaa80 0x30007ffffffffc0c 0x030007ffffffffc0

def z755 : W := mkw 0x4f6ee69aa0808000 0x04f6ee69aa080800 0xfffffffff3c0c007 0xffffffffff3c0c00

def z756 : W := mkw 0x4b42669aa0000000 0x04b42669aa000000 0xfff77ffff0000007 0xffff77ffff000000

def z757 : W := mkw 0x2638603604c380dd 0x02638603604c380d 0x2e30401c0dc303f8 0x52e30401c0dc303f

def z758 : W := mkw 0x5ffdedb66c3331bc 0x85ffdedb66c3331b 0x0e48b0c33c3333f8 0x80e48b0c33c3333f

def z759 : W := mkw 0x99c30fc8893c2120 0x899c30fc8893c212 0x91c70fc0003c0001 0x091c70fc0003c000

def z760 : W := mkw 0x2628701302c0c243 0x02628701302c0c24 0x2e38703f0fc0c3fe 0xf2e38703f0fc0c3f

def z761 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xb1b74f3ccc3003fd 0x7b1b74f3ccc3003f

def z762 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1ffcf3ccc3333ff 0xff1ffcf3ccc3333f

def z763 : W := mkw 0x143f822cc483b89c 0x8143f822cc483b89 0x4037003cc0033002 0x14037003cc003300

def z764 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e38701f0fc3c3f8 0xd2e38701f0fc3c3f

def z765 : W := mkw 0x8bc06dc0097c0160 0x08bc06dc0097c016 0xbfc04fc00dfc03fd 0x6bfc04fc00dfc03f

def z766 : W := mkw 0x2638707716c7c6df 0x42638707716c7c6d 0x2e38703f0fcfcffe 0xf2e38703f0fcfcff

def z767 : W := mkw 0x0b407cc002540340 0x00b407cc00254034 0xbfc07fc00ffc03fd 0xebfc07fc00ffc03f

def z768 : W := mkw 0x863dfdc006d6ab60 0x0863dfdc006d6ab6 0x703fffc00003fff6 0x1703fffc00003fff

def z769 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xdfff8820cffffc0f 0xfdfff8820cffffc0

def z770 : W := mkw 0x062a621a80000000 0x0062a621a8000000 0xfffffffff0000007 0xffffffffff000000

def z771 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x4e7f80000ffffc0a 0x94e7f80000ffffc0

def z772 : W := mkw 0x9b5376ecc74f32dc 0x89b5376ecc74f32d 0x4e7730fcc3cf3002 0x94e7730fcc3cf300

def z773 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x8fff80000ffffc08 0xd8fff80000ffffc0

def z774 : W := mkw 0x10930b0c8c322134 0x810930b0c8c32213 0xb1b74f1c0c0003f4 0x5b1b74f1c0c0003f

def z775 : W := mkw 0x8bc07dc04b7c1360 0x08bc07dc04b7c136 0xffc07fc0cffc33fd 0xeffc07fc0cffc33f

def z776 : W := mkw 0x8bc06d8009780160 0x08bc06d800978016 0xaf8047000df003f8 0x4af8047000df003f

def z777 : W := mkw 0x99c30fc8d93c3520 0xc99c30fc8d93c352 0xd1c78fc0f03c3c01 0x0d1c78fc0f03c3c0

def z778 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfff8023fffffc0b 0xfcfff8023fffffc0

def z779 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xffc8ffe3ffffffff 0xeffc8ffe3fffffff

def z780 : W := mkw 0x663cf03726c3c2df 0x0663cf03726c3c2d 0x2e38f03f3fc3c3fe 0xf2e38f03f3fc3c3f

def z781 : W := mkw 0x6f6cf49322c0c243 0x06f6cf49322c0c24 0x0e08300303c0c000 0x80e08300303c0c00

def z782 : W := mkw 0x0bc06d8009380120 0x00bc06d800938012 0xbfc07fc00ffc03fd 0xebfc07fc00ffc03f

def z783 : W := mkw 0x0200700002400240 0x0020070000240024 0xbf807f000fc003fd 0xebf807f000fc003f

def z784 : W := mkw 0x695696ada6c3c2df 0x0695696ada6c3c2d 0xd1c78fc0ffc3c3f9 0x0d1c78fc0ffc3c3f

def z785 : W := mkw 0x09c019400b3c0320 0x009c019400b3c032 0xbfc07fc00ffc03fd 0xebfc07fc00ffc03f

def z786 : W := mkw 0x8bc06d8009780160 0x08bc06d800978016 0xbfc07fc00df003fd 0xebfc07fc00df003f

def z787 : W := mkw 0xabc07dd30b7c4363 0x0abc07dd30b7c436 0xbfc07fc30ffc03fd 0xebfc07fc30ffc03f

def z788 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x6e38f03f0fc3fffe 0xf6e38f03f0fc3fff

def z789 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfff7fffff0000005 0x5fff7fffff000000

def z790 : W := mkw 0x1093030c8c222034 0x81093030c8c22203 0xa1b7471c0c0003fc 0x7a1b7471c0c0003f

def z791 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x3e3878ffffc3c3fe 0xf3e3878ffffc3c3f

def z792 : W := mkw 0x8bc07dc11b7c4762 0x48bc07dc11b7c476 0xbfc07fc00ffccffd 0xebfc07fc00ffccff

def z793 : W := mkw 0x6fffe69eadeaa855 0x06fffe69eadeaa85 0xafb7471c0dc00070 0x5afb7471c0dc0007

def z794 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e30703f0dc303fe 0x72e30703f0dc303f

def z795 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xdfffb8c00ffffc0f 0xfdfffb8c00ffffc0

def z796 : W := mkw 0x343f823fc483f89f 0x8343f823fc483f89 0x403f803fc003fc02 0x1403f803fc003fc0

def z797 : W := mkw 0x0bc079000b780360 0x00bc079000b78036 0xbfc07f000ffc03fd 0xebfc07f000ffc03f

def z798 : W := mkw 0x0210700406420254 0x0021070040642025 0x2e30701c0fc003fc 0xf2e30701c0fc003f

def z799 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcff780000ffffc09 0x5cff780000ffffc0

def z800 : W := mkw 0x10001965521557be 0xc10001965521557b 0x5048b8e3f23fffff 0xa5048b8e3f23ffff

def z801 : W := mkw 0x909119655f7f77fe 0xc909119655f7f77f 0x000000000ffffff8 0x0000000000ffffff

def z802 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfffb0c33ffffc0b 0xfcfffb0c33ffffc0

def z803 : W := mkw 0x06287033024142ca 0x006287033024142c 0x2e38703f0fc3c3fe 0xf2e38703f0fc3c3f

def z804 : W := mkw 0x1013022cc403309c 0x81013022cc403309 0xf1b74f3ccc0333ff 0x7f1b74f3ccc0333f

def z805 : W := mkw 0xc4ae9b5aab7c0360 0x0c4ae9b5aab7c036 0x403f803ffffc03fa 0x1403f803ffffc03f

def z806 : W := mkw 0x19c78b08c9383920 0x819c78b08c938392 0xd1870f00c0303001 0x0d1870f00c030300

def z807 : W := mkw 0x1d6e8b2cc19999bc 0x81d6e8b2cc19999b 0x3e48cf3cc3cccff4 0x83e48cf3cc3cccff

def z808 : W := mkw 0x22107037064342df 0x022107037064342d 0x2e30703f0fc303fe 0xf2e30703f0fc303f

def z809 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x6e78f03f0fc3c3ff 0xf6e78f03f0fc3c3f

def z810 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1b74f3ccc0333f6 0x5f1b74f3ccc0333f

def z811 : W := mkw 0x0dfd81000daaa820 0x00dfd81000daaa82 0xefffc7000ffffc7b 0xfefffc7000ffffc7

def z812 : W := mkw 0x2bc5f0370b696adf 0x02bc5f0370b696ad 0xe1c7f03f003c3ff5 0x0e1c7f03f003c3ff

def z813 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xffbffffff0000006 0x5ffbffffff000000

def z814 : W := mkw 0x6f6cf49323c8ca43 0x06f6cf49323c8ca4 0x0e48b0c333cccc00 0x80e48b0c333cccc0

def z815 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xa1b7471c0c0003f0 0x5a1b7471c0c0003f

def z816 : W := mkw 0x1093134d9e266636 0xc1093134d9e26663 0xa1fff7df3e0ccc70 0xda1fff7df3e0ccc7

def z817 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc8ffc33ffc03fd 0xebfc8ffc33ffc03f

def z818 : W := mkw 0x5fffe79eadaaa834 0x85fffe79eadaaa83 0xafb7471c0dc00070 0x5afb7471c0dc0007

def z819 : W := mkw 0x0bc074800b680240 0x00bc074800b68024 0xbfc07fc00ffc03fd 0xebfc07fc00ffc03f

def z820 : W := mkw 0x06387036064302dc 0x006387036064302d 0x2e38703f0fc303fe 0xf2e38703f0fc303f

def z821 : W := mkw 0x263df03706c3eadf 0x0263df03706c3ead 0x6e7ff03f0fffffff 0xf6e7ff03f0ffffff

def z822 : W := mkw 0x0638701206c28240 0x00638701206c2824 0x2e38703f0fc3c3fe 0xf2e38703f0fc3c3f

def z823 : W := mkw 0x8bc0658009680060 0x08bc065800968006 0xaf8047000dc003fc 0x6af8047000dc003f

def z824 : W := mkw 0x0d7c800004828000 0x00d7c80000482800 0xcfff80000ffffc0b 0xfcfff80000ffffc0

def z825 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfbf80000ffffc0a 0x5cfbf80000ffffc0

def z826 : W := mkw 0x000018615215578a 0x4000018615215578 0x5e48b8e3ffffff8f 0xe5e48b8e3ffffff8

def z827 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xffc8ffc00ffc03ff 0xeffc8ffc00ffc03f

def z828 : W := mkw 0x10820b2cc83111bc 0x810820b2cc83111b 0xf1b74f3ccc3003ff 0x7f1b74f3ccc3003f

def z829 : W := mkw 0x2200701602400255 0x0220070160240025 0x2e00701c0fc003fc 0xe2e00701c0fc003f

def z830 : W := mkw 0x32027b7fd25557ff 0xc32027b7fd25557f 0x30007ffff00003f4 0x030007ffff00003f

def z831 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfff800003fffc03 0x9cfff800003fffc0

def z832 : W := mkw 0x8bc07dc05b7c1760 0x48bc07dc05b7c176 0xbfc07fc00ffc3ffd 0xebfc07fc00ffc3ff

def z833 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0xefbf703f0fc3c3ff 0xfefbf703f0fc3c3f

def z834 : W := mkw 0x2210703706c3c2df 0x02210703706c3c2d 0x2e00703f0fc3c3fc 0xe2e00703f0fc3c3f

def z835 : W := mkw 0x643a023fa483c09f 0x0643a023fa483c09 0x0038003ff003c002 0x10038003ff003c00

def z836 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e30403c0fc3c3fe 0x72e30403c0fc3c3f

def z837 : W := mkw 0xc9c68fc8a93c0120 0x0c9c68fc8a93c012 0x91c70fc0003c0001 0x091c70fc0003c000

def z838 : W := mkw 0x8b4074c0034c0240 0x08b4074c0034c024 0xbfc07fc00fcc03fd 0xebfc07fc00fcc03f

def z839 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xbff77ffff0000005 0xfbff77ffff000000

def z840 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc07fe3fffc03fd 0xebfc07fe3fffc03f

def z841 : W := mkw 0x10020b2cc01111bc 0x810020b2cc01111b 0xb1b74f3cc00003f4 0x5b1b74f3cc00003f

def z842 : W := mkw 0xcfffe79aadeaa860 0x0cfffe79aadeaa86 0xafb7471c0dc00070 0x5afb7471c0dc0007

def z843 : W := mkw 0x80001961525557ea 0x480001961525557e 0x5048b8e3f23fffff 0xa5048b8e3f23ffff

def z844 : W := mkw 0x1093032ccc2330bc 0x81093032ccc2330b 0xe1b7473ccc0333fe 0x7e1b7473ccc0333f

def z845 : W := mkw 0x000010615205568a 0x4000010615205568 0x4048b0e3f23ffc0b 0xa4048b0e3f23ffc0

def z846 : W := mkw 0x2638703756c3d6df 0x42638703756c3d6d 0x2e38703f0fc3fffe 0xf2e38703f0fc3fff

def z847 : W := mkw 0x10930b6ddc3775be 0xc10930b6ddc3775b 0xf1ffcffffc3fffff 0x7f1ffcffffc3ffff

def z848 : W := mkw 0x2638707716c7c6df 0x42638707716c7c6d 0x2e3870ff3fc3c3fe 0xf2e3870ff3fc3c3f

def z849 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xffc07fe0cffc03ff 0xeffc07fe0cffc03f

def z850 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xaf8047000dc003f0 0x4af8047000dc003f

def z851 : W := mkw 0x0ded800009a8a800 0x00ded800009a8a80 0xcfcf800003fffc0b 0xacfcf800003fffc0

def z852 : W := mkw 0xcbc07dd22b7c0360 0x0cbc07dd22b7c036 0xbfc07fc33ffc03fd 0xebfc07fc33ffc03f

def z853 : W := mkw 0x4f6ee69aa1080800 0x04f6ee69aa108080 0xfffffffff00c0c07 0xffffffffff00c0c0

def z854 : W := mkw 0x2438103706c3c2df 0x02438103706c3c2d 0x0e38003f0fc3c3fa 0xf0e38003f0fc3c3f

def z855 : W := mkw 0x8bc17dc00b7c2360 0x08bc17dc00b7c236 0xffc77fc00ffc33fd 0xeffc77fc00ffc33f

def z856 : W := mkw 0x09d580000daaa800 0x009d580000daaa80 0xcfc780000ffffc09 0xecfc780000ffffc0

def z857 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x6e38f03fffc3c3fe 0xf6e38f03fffc3c3f

def z858 : W := mkw 0xc9c68fc8f93c1520 0x4c9c68fc8f93c152 0xd1c78fc0f03c3c01 0x0d1c78fc0f03c3c0

def z859 : W := mkw 0x8bc17dc00b7c2b60 0x08bc17dc00b7c2b6 0xbfc07fc00ffc3ffd 0xebfc07fc00ffc3ff

def z860 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xbfbf7ffff0000006 0xfbfbf7ffff000000

def z861 : W := mkw 0x643e823fa483c09f 0x0643e823fa483c09 0x003f003f0003c002 0x1003f003f0003c00

def z862 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xffc0ffc00ffc3ffd 0xeffc0ffc00ffc3ff

def z863 : W := mkw 0x2638701606c28255 0x02638701606c2825 0x2e38701c0fc3c3fe 0xf2e38701c0fc3c3f

def z864 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e38401c0fc3c3fa 0xf2e38401c0fc3c3f

def z865 : W := mkw 0x09c0090009380120 0x009c009000938012 0xbf804f000df003fd 0x6bf804f000df003f

def z866 : W := mkw 0x8bc07dc10b7c4362 0x08bc07dc10b7c436 0xbfc87fc30ffcc3fd 0xebfc87fc30ffcc3f

def z867 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1bf7f3fcc3333ff 0xff1bf7f3fcc3333f

def z868 : W := mkw 0xa63874f706c7c2df 0x0a63874f706c7c2d 0x2e3870ff0fc3c3fe 0xf2e3870ff0fc3c3f

def z869 : W := mkw 0x4f6ee69aa0808800 0x04f6ee69aa080880 0xfffffffff000cc07 0xffffffffff000cc0

def z870 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1b74f3ccc3033f5 0x5f1b74f3ccc3033f

def z871 : W := mkw 0x1093032c8c2320bc 0x81093032c8c2320b 0xe1b7473c0c3333ff 0x7e1b7473c0c3333f

def z872 : W := mkw 0x0000184152145702 0x4000018415214570 0x5048b8c3f23ffc0b 0xa5048b8c3f23ffc0

def z873 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xefffc0000fffffff 0xfefffc0000ffffff

def z874 : W := mkw 0xef6cf4d323ccc243 0x0ef6cf4d323ccc24 0x0e48b0c333ccc000 0x80e48b0c333ccc00

def z875 : W := mkw 0x0002022c8001009c 0x00002022c8001009 0xf1b74f3cc00003f7 0x7f1b74f3cc00003f

def z876 : W := mkw 0x2210702506c3c2df 0x02210702506c3c2d 0x2e30703c0fc3c3fe 0xf2e30703c0fc3c3f

def z877 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffff033300f 0xffffffffff033300

def z878 : W := mkw 0x343b023fd483f49f 0xc343b023fd483f49 0x403f803ff003fc02 0x1403f803ff003fc0

def z879 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfcf80000ffffc09 0x8cfcf80000ffffc0

def z880 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1f7cf3ccc3f3fff 0x7f1f7cf3ccc3f3ff

def z881 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xdfff88c0fffffc0b 0xfdfff88c0fffffc0

def z882 : W := mkw 0xc9c78fc8a93c2920 0x0c9c78fc8a93c292 0xd1c78fc0f03c3c01 0x0d1c78fc0f03c3c0

def z883 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0xbfb87f3f0fc3c3ff 0xfbfb87f3f0fc3c3f

def z884 : W := mkw 0x109119655fbfffbe 0xc109119655fbfffb 0x000000000ffffff8 0x0000000000ffffff

def z885 : W := mkw 0x2638701606c28255 0x02638701606c2825 0x2e38703f0fc003fe 0xf2e38703f0fc003f

def z886 : W := mkw 0x2639703706c3e2df 0x02639703706c3e2d 0x6e3f703f0fc3f3fe 0xf6e3f703f0fc3f3f

def z887 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc07fc00fcc03f4 0xcbfc07fc00fcc03f

def z888 : W := mkw 0x643e823ff483d49f 0x4643e823ff483d49 0x403f803ff003fc02 0x1403f803ff003fc0

def z889 : W := mkw 0x02106024044300dc 0x002106024044300d 0x2e30403c0dc303fe 0x72e30403c0dc303f

def z890 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e38403f0fc3c3fa 0x52e38403f0fc3c3f

def z891 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x7e78f8ffffffffff 0xf7e78f8fffffffff

def z892 : W := mkw 0x2dfd80160daaa815 0x02dfd80160daaa81 0xcfff801c0ffffc0b 0xfcfff801c0ffffc0

def z893 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbf804f000ffc03fd 0x6bf804f000ffc03f

def z894 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xffb74f3ccff333ff 0xfffb74f3ccff333f

def z895 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e78f03f0fcfcffe 0xf2e78f03f0fcfcff

def z896 : W := mkw 0x2638703606c382dd 0x02638703606c382d 0x2e30703c0fc303fe 0xf2e30703c0fc303f

def z897 : W := mkw 0x263874b706c3c2df 0x0263874b706c3c2d 0x3e387fff0fc3c3fe 0xf3e387fff0fc3c3f

def z898 : W := mkw 0x2638703756c3d6df 0x42638703756c3d6d 0x2e38703fffc3c3fe 0xf2e38703fffc3c3f

def z899 : W := mkw 0x00020b0880100120 0x000020b088010012 0xf1b74f3cc00003f7 0x7f1b74f3cc00003f

def z900 : W := mkw 0x263cf03706c3c2df 0x0263cf03706c3c2d 0x6e3ff03f0fc3c3fe 0xf6e3ff03f0fc3c3f

def z901 : W := mkw 0x643f823fa483e89f 0x0643f823fa483e89 0x403f803ff003fc02 0x1403f803ff003fc0

def z902 : W := mkw 0x0000104112044602 0x4000010411204460 0x5048b8e3f23ffc0f 0xa5048b8e3f23ffc0

def z903 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xffffffffffc0000f 0xfffffffffffc0000

def z904 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xffc07fc00fff33ff 0xeffc07fc00fff33f

def z905 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xafc077c00ffc03f8 0xcafc077c00ffc03f

def z906 : W := mkw 0x0200701202400240 0x0020070120240024 0x2e00703f0fc003fc 0xe2e00703f0fc003f

def z907 : W := mkw 0x4202669aa0000000 0x04202669aa000000 0xb1b77ffff0000004 0x5b1b77ffff000000

def z908 : W := mkw 0x2638701606c28255 0x02638701606c2825 0x2e30701c0dc003f4 0x52e30701c0dc003f

def z909 : W := mkw 0x000018615215578a 0x4000018615215578 0x7048f8e3fe3fffff 0xe7048f8e3fe3ffff

def z910 : W := mkw 0x10930b0c8c322134 0x810930b0c8c32213 0xa1b7471c0c3003f8 0x5a1b7471c0c3003f

def z911 : W := mkw 0x000018615215578a 0x4000018615215578 0xd1ffb8e3f23fff8f 0xfd1ffb8e3f23fff8

def z912 : W := mkw 0x462ee69aa0000000 0x0462ee69aa000000 0xf1bffffff0000007 0x7f1bffffff000000

def z913 : W := mkw 0xcbc4fdc02b7c0360 0x0cbc4fdc02b7c036 0xbfc0ffc03ffc03fd 0xebfc0ffc03ffc03f

def z914 : W := mkw 0x8bc07d800b780360 0x08bc07d800b78036 0xbf807f000ff003fd 0xebf807f000ff003f

def z915 : W := mkw 0x8bc075800b680260 0x08bc075800b68026 0xafc077000ffc03fd 0xeafc077000ffc03f

def z916 : W := mkw 0x309119655ef7f7ff 0xc309119655ef7f7f 0x000000000ffffff8 0x0000000000ffffff

def z917 : W := mkw 0xc2027ffbf25557ea 0x4c2027ffbf25557e 0x30007ffff00003f4 0x030007ffff00003f

def z918 : W := mkw 0x000018615215578a 0x4000018615215578 0x7078f8fff23fff8f 0xf7078f8fff23fff8

def z919 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xefffc03c0ffffc0f 0xfefffc03c0ffffc0

def z920 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e08703f0fc3c3fc 0x82e08703f0fc3c3f

def z921 : W := mkw 0x0080090008300120 0x0008009000830012 0xbf804f000ff003fd 0xebf804f000ff003f

def z922 : W := mkw 0x09d100000d2a2000 0x009d100000d2a200 0xcfff80000ffffc0b 0xfcfff80000ffffc0

def z923 : W := mkw 0x10930b2cdc3335bc 0xc10930b2cdc3335b 0xf1b7cf3cfc333fff 0x7f1b7cf3cfc333ff

def z924 : W := mkw 0x4b46e69aa0000000 0x04b46e69aa000000 0xf1f7fffff0000007 0x7f1f7fffff000000

def z925 : W := mkw 0x10930b2ddc3375be 0xc10930b2ddc3375b 0xf1fffffffc33ffff 0xff1fffffffc33fff

def z926 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1b77ffffc3333ff 0x7f1b77ffffc3333f

def z927 : W := mkw 0x2638707716c7c6df 0x42638707716c7c6d 0x6e78f0ff3fffffff 0xf6e78f0ff3ffffff

def z928 : W := mkw 0x10930b0ccc323134 0x810930b0ccc32313 0xf1b74f1ccc3033fd 0x7f1b74f1ccc3033f

def z929 : W := mkw 0x00820b28c83111a8 0x000820b28c83111a 0xf1b74f3ccc3333ff 0x7f1b74f3ccc3333f

def z930 : W := mkw 0xcf6cf4d3334c4642 0x4cf6cf4d3334c464 0x0e48b0c333cccc00 0x80e48b0c333cccc0

def z931 : W := mkw 0x000018655215579e 0x4000018655215579 0x7048f8fff23fffff 0xa7048f8fff23ffff

def z932 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xf1fffffff0000007 0x1f1fffffff000000

def z933 : W := mkw 0x8b407dc002540360 0x08b407dc00254036 0xbfc07fc00fc003fd 0xebfc07fc00fc003f

def z934 : W := mkw 0x10930b2ccdbbb9bc 0x810930b2ccdbbb9b 0xf1b74f3ccdf333ff 0x7f1b74f3ccdf333f

def z935 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1bf4f3cce33f3ff 0xff1bf4f3cce33f3f

def z936 : W := mkw 0x0012022c8403009c 0x00012022c8403009 0xa1b7473c0c0303fe 0x7a1b7473c0c0303f

def z937 : W := mkw 0x543f823ee483b89c 0x8543f823ee483b89 0x403f803ff003fc02 0x1403f803ff003fc0

def z938 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc8ffc00ffccffd 0xebfc8ffc00ffccff

def z939 : W := mkw 0x6f6ee69aa0c08041 0x06f6ee69aa0c0804 0xfffffffff1c00007 0xffffffffff1c0000

def z940 : W := mkw 0x8bc06d8009780160 0x08bc06d800978016 0xbfc04f000ffc03fd 0xebfc04f000ffc03f

def z941 : W := mkw 0x04b900000ca2a000 0x004b900000ca2a00 0xcfff80000ffffc0b 0xfcfff80000ffffc0

def z942 : W := mkw 0x2638603604c380dd 0x02638603604c380d 0x2e30403c0dc003f4 0x52e30403c0dc003f

def z943 : W := mkw 0x10120b2cc41311bc 0x810120b2cc41311b 0xf1b74f3ccc0303ff 0x7f1b74f3ccc0303f

def z944 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1b74f3ccc0003f7 0x7f1b74f3ccc0003f

def z945 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xbffffffff0000004 0xdbffffffff000000

def z946 : W := mkw 0x26287037024142df 0x026287037024142d 0x2e38703f0fc003fe 0xf2e38703f0fc003f

def z947 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xe1b7471c0c3333fb 0x7e1b7471c0c3333f

def z948 : W := mkw 0x02107025064342de 0x002107025064342d 0x2e38703f0fc3c3fe 0xf2e38703f0fc3c3f

def z949 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xe1b7473ccc3333fa 0x5e1b7473ccc3333f

def z950 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbf807fc00fc003fc 0xebf807fc00fc003f

def z951 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e38703f0fc0c3f4 0xd2e38703f0fc0c3f

def z952 : W := mkw 0x8bc075c00b6c0260 0x08bc075c00b6c026 0xafc077c00fcc03fc 0xeafc077c00fcc03f

def z953 : W := mkw 0x10930b2ccd3b39bc 0x810930b2ccd3b39b 0xf1b74f3ccc3f3fff 0x7f1b74f3ccc3f3ff

def z954 : W := mkw 0x263cf03706c3cadf 0x0263cf03706c3cad 0x2e38f03f0fc3cffe 0xf2e38f03f0fc3cff

def z955 : W := mkw 0x59c78f88e9383920 0x859c78f88e938392 0xd1c78fc0f03c3c01 0x0d1c78fc0f03c3c0

def z956 : W := mkw 0x00920b2c8c3301bc 0x000920b2c8c3301b 0xf1b74f3ccc3303ff 0x7f1b74f3ccc3303f

def z957 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc04fc00ffc03f9 0x4bfc04fc00ffc03f

def z958 : W := mkw 0x4d6e869aa0000000 0x04d6e869aa000000 0xd1ffbffff0000007 0xbd1ffbffff000000

def z959 : W := mkw 0x10930b2ddc3375be 0xc10930b2ddc3375b 0xf1b74f3ffc3333ff 0x7f1b74f3ffc3333f

def z960 : W := mkw 0x4202669aa0000000 0x04202669aa000000 0xf1fffffff0000007 0xff1fffffff000000

def z961 : W := mkw 0x0dfd80040daaa814 0x00dfd80040daaa81 0xefffc01c0ffffc7b 0xfefffc01c0ffffc7

def z962 : W := mkw 0x028071000a600260 0x0028071000a60026 0xaf8077000fc003fc 0xeaf8077000fc003f

def z963 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc07fc00dfc03f5 0x4bfc07fc00dfc03f

def z964 : W := mkw 0x2638603604c380dd 0x02638603604c380d 0x2e38703f0dc303fe 0xf2e38703f0dc303f

def z965 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc07fc00dc003f5 0xebfc07fc00dc003f

def z966 : W := mkw 0x82807dc00a740360 0x082807dc00a74036 0xbf807fc00ff003fd 0xebf807fc00ff003f

def z967 : W := mkw 0x10830b2cc83131bc 0x810830b2cc83131b 0xf1b74f3cc03033f7 0x7f1b74f3cc03033f

def z968 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e78f0ff3fc3c3fe 0xf2e78f0ff3fc3c3f

def z969 : W := mkw 0x0d6c800001888800 0x00d6c80000188880 0xcfff800003fffc0b 0xfcfff800003fffc0

def z970 : W := mkw 0x2638707716c7c6df 0x42638707716c7c6d 0x7e78f8ffffcfcfff 0xf7e78f8ffffcfcff

def z971 : W := mkw 0x8bc07dc05b7c1760 0x48bc07dc05b7c176 0xbfc07fc0fffc03fd 0xebfc07fc0fffc03f

def z972 : W := mkw 0x0b42668880000000 0x00b4266888000000 0xfffffffff0000007 0xffffffffff000000

def z973 : W := mkw 0x2628703702c1c2df 0x02628703702c1c2d 0x2e08703f0fc0c3fc 0xe2e08703f0fc0c3f

def z974 : W := mkw 0xcf6ee69aa1480040 0x0cf6ee69aa148004 0xfffffffff1c00007 0xffffffffff1c0000

def z975 : W := mkw 0x4f6ee69aa0400040 0x04f6ee69aa040004 0xfffffffffdc00077 0xffffffffffdc0007

def z976 : W := mkw 0x10930b2cccb3b9bc 0x810930b2cccb3b9b 0xf1b74f3ccc33ffff 0x7f1b74f3ccc33fff

def z977 : W := mkw 0x0002020880000000 0x0000202088000000 0xf1b74f3ccc0003ff 0x7f1b74f3ccc0003f

def z978 : W := mkw 0x0dfd80120daaa800 0x00dfd80120daaa80 0xcfff803f0ffffc0b 0xfcfff803f0ffffc0

def z979 : W := mkw 0x1093032c8c2320bc 0x81093032c8c2320b 0xa1b7471c0c0303f8 0x5a1b7471c0c0303f

def z980 : W := mkw 0x89c00dc0093c0120 0x089c00dc0093c012 0xbfc04fc00ffc03fd 0xebfc04fc00ffc03f

def z981 : W := mkw 0x89c01dc00b7c0360 0x089c01dc00b7c036 0x9fc00fc00ffc03f9 0xe9fc00fc00ffc03f

def z982 : W := mkw 0x2638707756c7d6df 0x42638707756c7d6d 0x6e78f0ffffcffffe 0xf6e78f0ffffcffff

def z983 : W := mkw 0x8bc07dc11b7c4762 0x48bc07dc11b7c476 0xbfc07fc33ffc03fd 0xebfc07fc33ffc03f

def z984 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x8ff700000ffffc09 0xf8ff700000ffffc0

def z985 : W := mkw 0x3639703746c3f2df 0x83639703746c3f2d 0x2e38703f0fc3f3fe 0xf2e38703f0fc3f3f

def z986 : W := mkw 0x2638703756c3d6df 0x42638703756c3d6d 0x6e78f03fffffffff 0xf6e78f03ffffffff

def z987 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xa1b7473c0c3333fe 0x7a1b7473c0c3333f

def z988 : W := mkw 0x0b40748002400240 0x00b4074800240024 0xaf8077000fc003fc 0xeaf8077000fc003f

def z989 : W := mkw 0x001000240403009c 0x0001000240403009 0x2e30403c0fc303fe 0xf2e30403c0fc303f

def z990 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc87fc00fffc3ff 0xebfc87fc00fffc3f

def z991 : W := mkw 0x89c20fc8893c0120 0x089c20fc8893c012 0xd1c70fc0c03c0001 0x0d1c70fc0c03c000

def z992 : W := mkw 0xaf6cf4d303ccca43 0x0af6cf4d303ccca4 0x0e48b0c303cccc00 0x80e48b0c303cccc0

def z993 : W := mkw 0x10930b6cdc3735bc 0xc10930b6cdc3735b 0xf1fffffffc3f3fff 0xff1fffffffc3f3ff

def z994 : W := mkw 0x0000184002140300 0x0000018400214030 0x5048b8e3f23fff8f 0xa5048b8e3f23fff8

def z995 : W := mkw 0x8bc07dc15b7c5762 0x48bc07dc15b7c576 0xffc8ffc3fffcfffd 0xeffc8ffc3fffcfff

def z996 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffff20ccc07 0xffffffffff20ccc0

def z997 : W := mkw 0x2638707706c7c2df 0x02638707706c7c2d 0x2e7870ff0fcfc3fe 0xf2e7870ff0fcfc3f

def z998 : W := mkw 0x4f6cf49222400240 0x04f6cf4922240024 0x0e48b0c333c00000 0x80e48b0c333c0000

def z999 : W := mkw 0x00120a2cc413119c 0x000120a2cc413119 0xf1b74f3ccc3333ff 0x7f1b74f3ccc3333f

def z1000 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1bfcf3ffc3333ff 0x7f1bfcf3ffc3333f

def z1001 : W := mkw 0x009109240c3321bc 0x0009109240c3321b 0xf1b74f3c0c3333ff 0x7f1b74f3c0c3333f

def z1002 : W := mkw 0x000018615215578a 0x4000018615215578 0x5048b8e3f23ffc03 0x85048b8e3f23ffc0

def z1003 : W := mkw 0x2638603604c380dd 0x02638603604c380d 0x2e38403c0fc3c3fe 0xf2e38403c0fc3c3f

def z1004 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xffc0ffc0fffc03fd 0xeffc0ffc0fffc03f

def z1005 : W := mkw 0x000018615215578a 0x4000018615215578 0x5048b8c3f23fff89 0x85048b8c3f23fff8

def z1006 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x6e38703f0ff3f3ff 0xf6e38703f0ff3f3f

def z1007 : W := mkw 0x000010210201428a 0x0000010210201428 0x5048b8e3f23fff8f 0xa5048b8e3f23fff8

def z1008 : W := mkw 0x8bc07dc05b7c1760 0x48bc07dc05b7c176 0xffc8ffc0ffffffff 0xeffc8ffc0fffffff

def z1009 : W := mkw 0x109119655e3777be 0xc109119655e3777b 0x000000000c3333f8 0x0000000000c3333f

def z1010 : W := mkw 0x10930b2ccd3b31bc 0x810930b2ccd3b31b 0xf1b74f3ccfff33ff 0x7f1b74f3ccfff33f

def z1011 : W := mkw 0x10930b0c8c322134 0x810930b0c8c32213 0xf1b74f1c0c3333ff 0x7f1b74f1c0c3333f

def z1012 : W := mkw 0x243a023f8483c09f 0x0243a023f8483c09 0x403f003fc003c002 0x1403f003fc003c00

def z1013 : W := mkw 0x2638603704c3c0df 0x02638603704c3c0d 0x2e38403f0dc3c3fe 0x72e38403f0dc3c3f

def z1014 : W := mkw 0x10930b6ccc3731bc 0x810930b6ccc3731b 0xf1f74ffccc3f33ff 0x7f1f74ffccc3f33f

def z1015 : W := mkw 0x4f6ee69aa1888800 0x04f6ee69aa188880 0xfffffffff1c00007 0xffffffffff1c0000

def z1016 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xffffcf000ffffc0f 0xfffffcf000ffffc0

def z1017 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc07fc00ffffffd 0xebfc07fc00ffffff

def z1018 : W := mkw 0x343a023fc483d09f 0x8343a023fc483d09 0x0038003fc003c002 0x10038003fc003c00

def z1019 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffff203c00f 0xffffffffff203c00

def z1020 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e38703f0dc003f6 0xf2e38703f0dc003f

def z1021 : W := mkw 0x8b407dc0035c0360 0x08b407dc0035c036 0x3e407fc00fcc03fc 0xe3e407fc00fcc03f

def z1022 : W := mkw 0x4dfd84802daaa800 0x04dfd84802daaa80 0xcfff80c03ffffc0b 0xfcfff80c03ffffc0

def z1023 : W := mkw 0x9bc17dc04b7c3360 0x89bc17dc04b7c336 0xbfc07fc00ffc33fd 0xebfc07fc00ffc33f

def z1024 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0x3e407fc00ffc03fc 0x83e407fc00ffc03f

def z1025 : W := mkw 0x0000084050141500 0x4000008405014150 0x5048b8e3f23ffc0f 0xa5048b8e3f23ffc0

def z1026 : W := mkw 0x143f822dd483fc9e 0xc143f822dd483fc9 0x403f803ff003fc02 0x1403f803ff003fc0

def z1027 : W := mkw 0x8bc5fdc00b7c2b60 0x08bc5fdc00b7c2b6 0xbfc77fc00ffc03fd 0xebfc77fc00ffc03f

def z1028 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xfff77fc00ffc03ff 0xffff77fc00ffc03f

def z1029 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffff003fc07 0xffffffffff003fc0

def z1030 : W := mkw 0x343b023f8483e09f 0x8343b023f8483e09 0x003f003f0003c002 0x1003f003f0003c00

def z1031 : W := mkw 0x043d80000482a800 0x0043d80000482a80 0x4e7f80000ffffc0b 0xf4e7f80000ffffc0

def z1032 : W := mkw 0x8bc4fdc00b7c0360 0x08bc4fdc00b7c036 0xffc7ffc00ffc03fd 0xeffc7ffc00ffc03f

def z1033 : W := mkw 0x10930b2cccb3b1bc 0x810930b2cccb3b1b 0xf1b74f3ccff3f3ff 0x7f1b74f3ccff3f3f

def z1034 : W := mkw 0x30930b2dccb3f1bf 0x830930b2dccb3f1b 0xf1b74f3ccc33f3ff 0x7f1b74f3ccc33f3f

def z1035 : W := mkw 0x04bd80000daaa800 0x004bd80000daaa80 0x4e3f80000ffffc0a 0xf4e3f80000ffffc0

def z1036 : W := mkw 0x1dfd81040daaa834 0x81dfd81040daaa83 0xcfff80000ffffc7b 0xfcfff80000ffffc7

def z1037 : W := mkw 0x8bc4fdc00b7c0b60 0x08bc4fdc00b7c0b6 0xbfc0ffc00ffc0ffd 0xebfc0ffc00ffc0ff

def z1038 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1b74f3cc03333f7 0x1f1b74f3cc03333f

def z1039 : W := mkw 0x6f6cf49322404243 0x06f6cf4932240424 0x0e48b0c330000000 0x80e48b0c33000000

def z1040 : W := mkw 0x20001865525557df 0x420001865525557d 0x5048b8e3f23fffff 0xa5048b8e3f23ffff

def z1041 : W := mkw 0x00001861525557ca 0x400001861525557c 0x5048b8e3ffffffff 0xa5048b8e3fffffff

def z1042 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xb1b74f3ccc3333fc 0x5b1b74f3ccc3333f

def z1043 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e30703f0fc003fc 0xf2e30703f0fc003f

def z1044 : W := mkw 0x82007dc002540360 0x082007dc00254036 0x3e407fc00ffc03fd 0xe3e407fc00ffc03f

def z1045 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfb700000ffffc0b 0x7cfb700000ffffc0

def z1046 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xb1b74f1c0c3333fd 0x7b1b74f1c0c3333f

def z1047 : W := mkw 0x92027fedd25557fe 0xc92027fedd25557f 0x30007ffff00003f4 0x030007ffff00003f

def z1048 : W := mkw 0x000000215001548a 0x4000000215001548 0x5048b8e3f23ffc0f 0xa5048b8e3f23ffc0

def z1049 : W := mkw 0x10830b08c8303120 0x810830b08c830312 0xf1b74f3ccc3033ff 0x7f1b74f3ccc3033f

def z1050 : W := mkw 0x10930b0c8c322134 0x810930b0c8c32213 0xf1b74f3ccc3003ff 0x7f1b74f3ccc3003f

def z1051 : W := mkw 0x8bc07dd20b7c0360 0x08bc07dd20b7c036 0xbfc07fff0ffc03fd 0xebfc07fff0ffc03f

def z1052 : W := mkw 0x04b900000daaa800 0x004b900000daaa80 0xcfbf00000ffffc0b 0xfcfbf00000ffffc0

def z1053 : W := mkw 0xd9c78fc8e93c3120 0x8d9c78fc8e93c312 0xd1c78fc0f03c3001 0x0d1c78fc0f03c300

def z1054 : W := mkw 0x8bc5fdc05b7c3f60 0x48bc5fdc05b7c3f6 0xffc7ffc0fffc3ffd 0xeffc7ffc0fffc3ff

def z1055 : W := mkw 0x10930b2ccdbbb9bc 0x810930b2ccdbbb9b 0xf1ffcf3ccfffffff 0xff1ffcf3ccffffff

def z1056 : W := mkw 0x99c30f88c9383120 0x899c30f88c938312 0xd1870f00c0303001 0x0d1870f00c030300

def z1057 : W := mkw 0x2639703706c3eadf 0x02639703706c3ead 0x2e38703f0fc3fffe 0xf2e38703f0fc3fff

def z1058 : W := mkw 0x000018615215578a 0x4000018615215578 0xf1c8ffe3f23fff8f 0xef1c8ffe3f23fff8

def z1059 : W := mkw 0x2638703716c3c6df 0x42638703716c3c6d 0x2e38f03f3fc3cffe 0xf2e38f03f3fc3cff

def z1060 : W := mkw 0x89c019400b7c0360 0x089c019400b7c036 0xbfc04f000ffc03fd 0xebfc04f000ffc03f

def z1061 : W := mkw 0xcf6cf4d223cc8a40 0x0cf6cf4d223cc8a4 0x0e48b0c333cccc00 0x80e48b0c333cccc0

def z1062 : W := mkw 0x2638703756c3d6df 0x42638703756c3d6d 0x7e78f8ffffc3ffff 0xf7e78f8ffffc3fff

def z1063 : W := mkw 0x19c30b08c9383120 0x819c30b08c938312 0xd1c70f00c03c3001 0x0d1c70f00c03c300

def z1064 : W := mkw 0x043800240483809c 0x0043800240483809 0x2e30403c0dc303fe 0x72e30403c0dc303f

def z1065 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x7e38783fcfc3c3ff 0xf7e38783fcfc3c3f

def z1066 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1b74f3cce3fffff 0x7f1b74f3cce3ffff

def z1067 : W := mkw 0x028079400a740360 0x0028079400a74036 0xbfc07fc00ffc03fd 0xebfc07fc00ffc03f

def z1068 : W := mkw 0x02007024024102dc 0x002007024024102d 0x2e00703c0fc003fc 0xe2e00703c0fc003f

def z1069 : W := mkw 0x2638703746c3d2df 0x02638703746c3d2d 0x6e38703fcfc3f3fe 0xf6e38703fcfc3f3f

def z1070 : W := mkw 0x8bc5fdc00b7c2b60 0x08bc5fdc00b7c2b6 0xffcfffc00fffffff 0xeffcfffc00ffffff

def z1071 : W := mkw 0x00820b0888300120 0x000820b088830012 0xb1b74f1c0c3003fd 0x7b1b74f1c0c3003f

def z1072 : W := mkw 0x82807dc00b7c0360 0x082807dc00b7c036 0x3e007fc00ffc03fc 0xe3e007fc00ffc03f

def z1073 : W := mkw 0x0200790002500360 0x0020079000250036 0x3e007f000fc003fc 0xe3e007f000fc003f

def z1074 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbf807fc00ffc03fc 0x4bf807fc00ffc03f

def z1075 : W := mkw 0x8bc07dc01b7c0760 0x48bc07dc01b7c076 0xbfc0ffc03ffc0ffd 0xebfc0ffc03ffc0ff

def z1076 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x3e7878ff0fc3c3ff 0xf3e7878ff0fc3c3f

def z1077 : W := mkw 0x8bc07dc11b7c4762 0x48bc07dc11b7c476 0xffc8ffe3fffccfff 0xeffc8ffe3fffccff

def z1078 : W := mkw 0x143b022cc483b09c 0x8143b022cc483b09 0x403f003cc003f002 0x1403f003cc003f00

def z1079 : W := mkw 0x09d100000daaa800 0x009d100000daaa80 0xcff700000ffffc0b 0xfcff700000ffffc0

def z1080 : W := mkw 0x10930b6cdc3735bc 0xc10930b6cdc3735b 0xf1b74ffcfc3333ff 0x7f1b74ffcfc3333f

def z1081 : W := mkw 0x063860360483809c 0x0063860360483809 0x2e38703f0fc3c3fe 0xf2e38703f0fc3c3f

def z1082 : W := mkw 0x62027efff25557df 0x462027efff25557d 0x30007ffff00003f4 0x030007ffff00003f

def z1083 : W := mkw 0x10930b6cdc3735bc 0xc10930b6cdc3735b 0xf1ffcffcfe3fffff 0xff1ffcffcfe3ffff

def z1084 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xfffffffffc0003ff 0xffffffffffc0003f

def z1085 : W := mkw 0x0628701202400240 0x0062870120240024 0x2e30701c0fc003fc 0xf2e30701c0fc003f

def z1086 : W := mkw 0x743f823fe483f09f 0x8743f823fe483f09 0x403f803ff003f002 0x1403f803ff003f00

def z1087 : W := mkw 0x0dfd84800daaa800 0x00dfd84800daaa80 0xdfff8fc00ffffc0b 0xfdfff8fc00ffffc0

def z1088 : W := mkw 0x49468688a0000000 0x049468688a000000 0xf1fffffff0000007 0xff1fffffff000000

def z1089 : W := mkw 0x4f6ee69aa1888800 0x04f6ee69aa188880 0xfffffffff3fffc0f 0xffffffffff3fffc0

def z1090 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbfc87fe30ffc03ff 0xebfc87fe30ffc03f

def z1091 : W := mkw 0x343b023ec483b09d 0x8343b023ec483b09 0x4037003cc0033002 0x14037003cc003300

def z1092 : W := mkw 0x10930b2ddc3375be 0xc10930b2ddc3375b 0xf1ffcf3ffe3fffff 0xff1ffcf3ffe3ffff

def z1093 : W := mkw 0x2638701606c28255 0x02638701606c2825 0x2e30401c0fc003f8 0x52e30401c0fc003f

def z1094 : W := mkw 0x10020b2cc01111bc 0x810020b2cc01111b 0xf1b74f3cc03333ff 0x7f1b74f3cc03333f

def z1095 : W := mkw 0x2438102506c3c2df 0x02438102506c3c2d 0x2e38403c0fc3c3fe 0xf2e38403c0fc3c3f

def z1096 : W := mkw 0x0638702406c382dc 0x00638702406c382d 0x2e38703c0fc3c3fe 0xf2e38703c0fc3c3f

def z1097 : W := mkw 0x0200748002400240 0x0020074800240024 0x3e007fc00fc003fc 0xe3e007fc00fc003f

def z1098 : W := mkw 0xcf6cf4d222440240 0x0cf6cf4d22244024 0x0e48b0c330000000 0x80e48b0c33000000

def z1099 : W := mkw 0x0bc07d800a700360 0x00bc07d800a70036 0xbfc07fc00ff003fd 0xebfc07fc00ff003f

def z1100 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1bfcf3ccc33ffff 0x7f1bfcf3ccc33fff

def z1101 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e38703f0ffffffe 0xf2e38703f0ffffff

def z1102 : W := mkw 0x00001961521557aa 0x400001961521557a 0x7048ffe3f23fffff 0xa7048ffe3f23ffff

def z1103 : W := mkw 0x10130b2cc41331bc 0x810130b2cc41331b 0xf1b74f3cc00333f7 0x7f1b74f3cc00333f

def z1104 : W := mkw 0x99c20fc8c93c1120 0x899c20fc8c93c112 0x91c00fc0c03c0001 0x091c00fc0c03c000

def z1105 : W := mkw 0x000018615215578a 0x4000018615215578 0x4048b0e3f23fff8a 0x84048b0e3f23fff8

def z1106 : W := mkw 0x0dec800009280000 0x00dec80000928000 0xcfff80000ffffc0b 0xfcfff80000ffffc0

def z1107 : W := mkw 0x8bc07dc05b7c1760 0x48bc07dc05b7c176 0xffc8ffe3fffc3fff 0xeffc8ffe3fffc3ff

def z1108 : W := mkw 0x8200758002400260 0x0820075800240026 0x2e0077000fc003fc 0xe2e0077000fc003f

def z1109 : W := mkw 0x2638601604c28055 0x02638601604c2805 0x2e30401c0dc003fc 0x72e30401c0dc003f

def z1110 : W := mkw 0x22007037024142df 0x022007037024142d 0x2e00703f0dc003f4 0x42e00703f0dc003f

def z1111 : W := mkw 0x0d6e820880000000 0x00d6e82088000000 0xfffffffff0000007 0xffffffffff000000

def z1112 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1f77ffccc3333ff 0xff1f77ffccc3333f

def z1113 : W := mkw 0x8bc07dc00b7c0360 0x08bc07dc00b7c036 0xbff07ffc0ffc03ff 0xfbff07ffc0ffc03f

def z1114 : W := mkw 0x2638703706c3c2df 0x02638703706c3c2d 0x2e78703f0fffc3ff 0xf2e78703f0fffc3f

def z1115 : W := mkw 0x1093032c8c2320bc 0x81093032c8c2320b 0xf1b74f3ccc0303ff 0x7f1b74f3ccc0303f

def z1116 : W := mkw 0x90930b6ccd3f31bc 0x890930b6ccd3f31b 0xf1b74f3ccc3f33ff 0x7f1b74f3ccc3f33f

def z1117 : W := mkw 0x0002020880000000 0x0000202088000000 0xf1b77ffff0000007 0x7f1b77ffff000000

def z1118 : W := mkw 0x2638701706c2c257 0x02638701706c2c25 0x2e38701f0fc0c3fc 0xf2e38701f0fc0c3f

def z1119 : W := mkw 0xc9c20fc8a93c0120 0x0c9c20fc8a93c012 0x91c00fc0f03c0001 0x091c00fc0f03c000

def z1120 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xf1b74f1ccc3333f9 0x5f1b74f1ccc3333f

def z1121 : W := mkw 0x10930b6cdc3735bc 0xc10930b6cdc3735b 0xf1b74f3ccc3f3fff 0x7f1b74f3ccc3f3ff

def z1122 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xffb77ffff0000007 0x7ffb77ffff000000

def z1123 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0xcfffb0230ffffc0f 0xfcfffb0230ffffc0

def z1124 : W := mkw 0x0dfd80000daaa800 0x00dfd80000daaa80 0x8fbf00000ffffc0a 0xf8fbf00000ffffc0

def z1125 : W := mkw 0x0093022c8c23209c 0x00093022c8c23209 0xf1b74f3ccc3333ff 0x7f1b74f3ccc3333f

def z1126 : W := mkw 0x4dfd80122daaa800 0x04dfd80122daaa80 0xcfff80033ffffc0b 0xfcfff80033ffffc0

def z1127 : W := mkw 0x10930b2ccc3331bc 0x810930b2ccc3331b 0xb1b74f3ccc0303fe 0x7b1b74f3ccc0303f

def z1128 : W := mkw 0x000018615215578a 0x4000018615215578 0x1048b8e3f23fff8c 0x81048b8e3f23fff8

def z1129 : W := mkw 0x0200700002400240 0x0020070000240024 0x2e30703c0fc003fe 0xf2e30703c0fc003f

def z1130 : W := mkw 0x000018615215578a 0x4000018615215578 0x5048b8e3f03fff87 0x05048b8e3f03fff8

def z1131 : W := mkw 0x4f6ee69aa0000000 0x04f6ee69aa000000 0xdfffbffff0000003 0x9dfffbffff000000

def z1132 : W := mkw 0x043810250683c29e 0x0043810250683c29 0x2e38703f0fc3c3fe 0xf2e38703f0fc3c3f

def z1133 : W := mkw 0x6f6cf4d332c4c643 0x46f6cf4d332c4c64 0x0e48b0c333cccc00 0x80e48b0c333cccc0

def z1134 : W := mkw 0x10930b2dcc3371be 0x810930b2dcc3371b 0xf1bf4f3fcc33f3ff 0x7f1bf4f3fcc33f3f

def z1135 : W := mkw 0x8bc07dc11b7c4762 0x48bc07dc11b7c476 0xffc8ffc33fffffff 0xeffc8ffc33ffffff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z4,z8,z5,z6])],[(0,[z1,z2,z9,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z10])],[(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z1,z12,z2,z3,z13,z5,z6]),(0,[z1,z2,z3,z14,z4,z5,z6])],[(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z16,z2,z3,z4,z17,z5,z6]),(0,[z1,z18,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z21,z22]),(0,[z1,z23,z2,z3,z4,z5,z6]),(0,[z1,z24,z2,z25,z3,z4,z5])],[(0,[z1,z2,z26,z3,z4,z5,z6])],[(0,[z27,z1,z2,z28,z4,z5,z6]),(0,[z1,z29,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z30,z6]),(0,[z1,z2,z3,z4,z5,z6,z31])],[(0,[z1,z2,z3,z4,z5,z32,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z1,z35,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z37,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z38,z6]),(0,[z1,z39,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z40]),(0,[z41,z1,z2,z3,z4,z5,z6])],[(0,[z42,z1,z2,z3,z4,z43,z6]),(0,[z1,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z45,z4,z5,z6]),(0,[z1,z2,z3,z46,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z6]),(0,[z1,z2,z3,z4,z5,z48,z6])],[(0,[z1,z2,z49,z3,z4,z5,z6]),(0,[z50,z1,z2,z3,z4,z5,z6])],[(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z52,z2,z3,z4,z5,z6]),(0,[z1,z53,z2,z3,z4,z5,z6]),(1,[z1,z54,z3,z4,z55,z6]),(0,[z1,z56,z2,z3,z4,z5,z6])],[(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z1,z58,z2,z4,z5,z6,z59])],[(0,[z1,z2,z3,z4,z60,z5,z6]),(0,[z1,z2,z3,z4,z61,z5,z6]),(0,[z1,z62,z2,z3,z4,z5,z6]),(1,[z1,z58,z2,z4,z5,z59]),(0,[z1,z2,z63,z3,z4,z5,z6])],[(0,[z1,z2,z64,z65,z4,z5,z6]),(0,[z1,z2,z3,z66,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z67,z6])],[(0,[z1,z2,z3,z4,z5,z68,z6]),(1,[z1,z12,z2,z13,z5,z6])]],
   [[(0,[z1,z69,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z70,z5,z6]),(0,[z1,z2,z71,z3,z4,z5,z6]),(0,[z1,z72,z2,z3,z4,z5,z6]),(0,[z1,z73,z2,z3,z4,z74,z6]),(1,[z1,z75,z2,z3,z4,z5])],[(0,[z1,z2,z9,z3,z65,z4,z6]),(0,[z1,z2,z3,z76,z4,z5,z6]),(0,[z77,z1,z2,z3,z76,z5,z6]),(0,[z1,z24,z2,z3,z4,z5,z21]),(0,[z1,z78,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z79])],[(0,[z80,z2,z81,z3,z4,z5,z6]),(0,[z1,z2,z82,z3,z4,z5,z6]),(0,[z1,z2,z83,z81,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z84,z6]),(0,[z1,z85,z2,z3,z4,z5,z6])],[(0,[z80,z1,z2,z3,z86,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z87]),(0,[z1,z88,z2,z3,z4,z5,z22]),(0,[z1,z12,z2,z36,z4,z5,z6]),(0,[z89,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z90,z6]),(0,[z1,z16,z3,z4,z5,z91,z6]),(0,[z1,z2,z3,z4,z92,z5,z6])],[(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z27,z2,z3,z4,z5,z21,z6]),(0,[z1,z94,z2,z3,z95,z5,z6])],[(0,[z1,z2,z3,z4,z96,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z5,z6]),(0,[z27,z1,z2,z3,z61,z5,z6]),(1,[z1,z98,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z99,z5,z100])],[(1,[z0,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z101,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z102,z6]),(0,[z1,z103,z2,z3,z104,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z105]),(0,[z1,z106,z2,z3,z4,z5,z6]),(0,[z1,z2,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z108])],[(0,[z42,z1,z16,z3,z4,z5,z6]),(0,[z1,z109,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z110,z4,z5,z6]),(0,[z1,z111,z2,z3,z4,z5,z6]),(0,[z1,z2,z83,z3,z4,z74,z6]),(0,[z1,z2,z112,z3,z4,z5,z6])],[(0,[z80,z1,z2,z3,z4,z5,z6]),(0,[z113,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z114,z3,z4,z5,z6]),(0,[z1,z2,z3,z115,z4,z5,z6])],[(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z100,z117]),(0,[z1,z2,z3,z118,z4,z5,z6]),(0,[z1,z119,z2,z3,z4,z5,z6]),(0,[z1,z103,z2,z3,z4,z120,z6])],[(0,[z1,z2,z3,z4,z5,z6,z121]),(0,[z1,z122,z2,z3,z4,z5,z6]),(1,[z1,z123,z2,z3,z5,z6])],[(0,[z1,z2,z3,z124,z4,z5,z6]),(0,[z1,z2,z125,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z126,z6]),(0,[z1,z127,z2,z3,z4,z5,z6]),(0,[z1,z128,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z86,z4,z5,z6]),(0,[z1,z129,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z130,z4,z5,z6]),(0,[z1,z131,z2,z3,z4,z5,z6]),(0,[z132,z1,z2,z3,z133,z5,z6]),(0,[z1,z2,z3,z104,z133,z5,z6]),(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z134,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z135]),(0,[z1,z2,z136,z3,z4,z5,z6])]],
   [[(0,[z42,z1,z137,z3,z4,z5,z6]),(0,[z138,z2,z3,z65,z4,z5,z6]),(0,[z1,z2,z3,z65,z4,z5,z6]),(1,[z1,z139,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z117]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z141,z6])],[(0,[z1,z142,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z143,z6]),(0,[z1,z24,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z144,z4,z5,z6])],[(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z146,z3,z4,z5,z6,z22]),(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z1,z148,z2,z3,z4,z5,z6])],[(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z64,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z150]),(0,[z1,z151,z2,z36,z3,z5,z6]),(0,[z1,z152,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z153,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z154]),(0,[z1,z155,z2,z3,z4,z5,z6])],[(0,[z1,z2,z64,z81,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z156,z6]),(0,[z1,z2,z3,z4,z5,z6,z10])],[(0,[z1,z2,z157,z3,z4,z5,z6]),(0,[z1,z58,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z6])],[(0,[z1,z159,z2,z3,z4,z5,z6]),(0,[z160,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z161]),(0,[z1,z162,z2,z3,z4,z5,z6]),(0,[z1,z163,z2,z3,z4,z13,z5]),(0,[z1,z2,z3,z164,z4,z5,z6]),(0,[z1,z2,z3,z104,z4,z120,z6])],[(0,[z1,z2,z3,z4,z43,z5,z6]),(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z1,z54,z2,z166,z4,z5,z6]),(0,[z1,z2,z3,z4,z167,z13,z5]),(0,[z1,z168,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z169,z4,z5,z170])]],
   [[(1,[z1,z2,z3,z171,z5,z6]),(0,[z1,z2,z3,z172,z4,z5,z6]),(0,[z1,z2,z28,z3,z4,z5,z6]),(0,[z1,z173,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z174])],[(0,[z42,z0,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z175,z6]),(0,[z1,z2,z3,z4,z5,z176,z6])],[(0,[z1,z2,z3,z4,z177,z5,z6]),(0,[z1,z2,z178,z3,z4,z5,z6]),(0,[z1,z58,z24,z2,z3,z4,z5]),(0,[z1,z2,z3,z120,z5,z179,z6])],[(0,[z1,z180,z2,z3,z4,z5,z6]),(0,[z1,z181,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z182,z5,z6]),(0,[z1,z2,z3,z4,z183,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z184]),(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z103,z2,z3,z4,z179,z6])],[(0,[z1,z2,z3,z4,z5,z186,z6]),(0,[z1,z2,z81,z4,z5,z74,z6]),(0,[z2,z3,z4,z5,z21,z6,z117]),(0,[z1,z2,z3,z187,z4,z5,z6]),(0,[z1,z2,z3,z188,z4,z5,z6])],[(0,[z1,z12,z106,z2,z3,z5,z6]),(0,[z1,z2,z189,z3,z4,z5,z6]),(1,[z1,z2,z3,z169,z5,z170]),(0,[z1,z2,z3,z190,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z191]),(1,[z1,z192,z95,z4,z5,z6]),(0,[z1,z2,z37,z4,z13,z5,z6]),(0,[z1,z73,z2,z4,z5,z193,z6])]],
   [[(0,[z1,z2,z81,z95,z4,z5,z6]),(0,[z1,z2,z3,z194,z4,z5,z6]),(0,[z195,z1,z2,z3,z4,z5,z6]),(0,[z196,z1,z2,z3,z4,z5,z6]),(1,[z1,z197,z2,z3,z4,z198])],[(0,[z1,z2,z3,z4,z5,z199,z6]),(0,[z77,z1,z2,z200,z4,z5,z6]),(0,[z1,z2,z3,z4,z201,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z6]),(0,[z1,z2,z83,z3,z4,z203,z6])],[(0,[z2,z3,z4,z17,z5,z204,z6]),(0,[z1,z2,z3,z4,z5,z205,z6]),(0,[z1,z2,z3,z169,z4,z99,z5])],[(0,[z206,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z133,z207,z5,z6]),(1,[z1,z2,z166,z4,z5,z6])],[(0,[z208,z1,z209,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z3,z4,z211,z5,z6])],[(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z55,z17,z6]),(0,[z1,z213,z2,z3,z4,z5,z6])],[],[(1,[z1,z2,z3,z4,z5,z214]),(0,[z1,z139,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z215,z6]),(0,[z1,z73,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z104,z4,z179,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z216]),(0,[z1,z2,z217,z3,z4,z5,z6])],[(0,[z1,z218,z2,z3,z4,z5,z6]),(0,[z1,z219,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z220,z5,z6]),(1,[z1,z151,z3,z187,z5,z6]),(0,[z1,z146,z2,z3,z4,z5,z221]),(0,[z1,z2,z3,z4,z222,z5,z6]),(0,[z1,z223,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z224]),(0,[z1,z2,z3,z4,z5,z100,z21]),(0,[z1,z2,z3,z4,z5,z225,z6]),(0,[z1,z2,z3,z4,z226,z5,z6])],[(0,[z1,z2,z3,z227,z95,z5,z6]),(0,[z1,z2,z228,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z203,z5,z6])],[(0,[z1,z137,z3,z4,z5,z91,z6]),(0,[z1,z2,z3,z4,z204,z91,z6]),(0,[z1,z2,z3,z4,z229,z5,z6])],[(0,[z1,z2,z3,z230,z4,z5,z6]),(0,[z1,z231,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z221,z6,z22])],[(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z1,z233,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z234,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z235])],[(0,[z1,z94,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z4,z13,z5,z6]),(0,[z1,z12,z2,z3,z5,z170,z6]),(0,[z1,z2,z3,z4,z236,z5,z6]),(0,[z1,z237,z2,z4,z5,z6,z198])]],
   [[(0,[z238,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z239,z5,z6]),(0,[z1,z2,z3,z4,z240,z5,z6]),(0,[z241,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z242,z3,z4,z5,z6])],[(0,[z1,z243,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z244,z6]),(0,[z208,z1,z2,z3,z245,z5,z6]),(0,[z1,z2,z3,z4,z5,z221,z117]),(0,[z1,z2,z3,z246,z95,z4,z5])],[(0,[z247,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z172,z4,z5,z6]),(0,[z1,z2,z3,z4,z248,z5,z6]),(0,[z1,z2,z249,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z250])],[(0,[z1,z2,z3,z4,z251,z5,z6]),(0,[z1,z2,z3,z4,z252,z5,z6]),(0,[z1,z2,z209,z3,z4,z5,z6]),(0,[z1,z2,z166,z3,z4,z5,z6]),(0,[z253,z1,z2,z3,z4,z5,z6]),(0,[z1,z254,z2,z3,z4,z5,z6]),(0,[z255,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z256,z3,z4,z5,z6]),(1,[z1,z2,z3,z257,z5,z6]),(0,[z1,z12,z24,z2,z3,z5,z6]),(0,[z1,z24,z2,z3,z4,z5,z258])],[(0,[z1,z2,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z133,z5,z179,z6]),(0,[z1,z2,z3,z4,z5,z259,z6]),(0,[z1,z260,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z250,z59]),(0,[z1,z2,z3,z4,z5,z6,z261])],[(0,[z1,z2,z83,z3,z4,z55,z6]),(0,[z1,z146,z2,z25,z3,z4,z5]),(0,[z1,z88,z2,z3,z262,z5,z6]),(0,[z1,z2,z25,z4,z5,z193,z6]),(0,[z1,z2,z263,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z264])],[(0,[z1,z2,z3,z4,z5,z6,z265]),(1,[z208,z2,z3,z4,z204,z6]),(0,[z1,z2,z3,z4,z266,z5,z6])]],
   [[(0,[z208,z1,z2,z3,z267,z5,z6]),(0,[z268,z1,z2,z3,z4,z5,z6])],[(0,[z269,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z76,z207,z5,z6]),(0,[z1,z2,z3,z4,z5,z270,z6]),(0,[z1,z123,z2,z3,z5,z6,z59]),(0,[z1,z197,z2,z3,z4,z5,z6])],[(0,[z1,z271,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z272,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z21,z6]),(0,[z1,z2,z3,z4,z5,z273,z6]),(0,[z1,z274,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z275,z6]),(0,[z1,z276,z2,z3,z4,z5,z6]),(0,[z1,z12,z151,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z277,z5,z6]),(0,[z1,z278,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z10,z198])],[(0,[z1,z2,z3,z4,z171,z5,z6]),(0,[z1,z2,z3,z4,z133,z5,z6]),(0,[z1,z2,z279,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z280,z5,z6]),(0,[z1,z2,z3,z4,z5,z281,z6]),(0,[z1,z2,z3,z4,z5,z282,z6])],[(0,[z283,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z81,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z284]),(0,[z1,z197,z2,z3,z4,z5,z198])],[(0,[z1,z2,z3,z4,z5,z21,z198]),(0,[z1,z2,z285,z3,z4,z5,z6])],[(0,[z1,z2,z25,z3,z4,z5,z117]),(0,[z1,z2,z3,z286,z4,z5,z6]),(0,[z1,z2,z3,z287,z4,z5,z6]),(0,[z1,z2,z288,z3,z4,z5,z6])],[(0,[z1,z16,z2,z3,z4,z5,z6]),(0,[z1,z54,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z17,z5,z6]),(0,[z1,z2,z3,z289,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z22])]],
   [[(0,[z1,z2,z3,z4,z290,z5,z6]),(1,[z138,z2,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z291,z5,z6]),(0,[z1,z58,z2,z3,z4,z5,z59])],[(0,[z1,z2,z292,z3,z4,z5,z6]),(0,[z1,z106,z2,z36,z3,z5,z6]),(0,[z1,z2,z3,z293,z4,z5,z6])],[(0,[z1,z2,z3,z169,z4,z5,z21]),(0,[z1,z294,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z295,z6])],[(0,[z1,z2,z3,z296,z4,z5,z6]),(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z1,z298,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z299,z4,z5,z6]),(0,[z138,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z300]),(1,[z1,z73,z2,z4,z74,z6]),(0,[z301,z1,z2,z3,z4,z5,z6])],[(1,[z80,z2,z81,z4,z5,z6]),(0,[z1,z302,z2,z3,z4,z5,z6])],[(0,[z1,z54,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z303,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z304,z5,z6])],[(0,[z1,z2,z3,z4,z305,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z306,z6]),(0,[z1,z2,z3,z4,z307,z5,z6]),(0,[z1,z308,z2,z3,z4,z5,z6]),(0,[z1,z151,z2,z3,z4,z5,z309]),(0,[z1,z2,z310,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z311,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z312])],[(0,[z1,z2,z3,z313,z4,z5,z6]),(0,[z138,z80,z2,z3,z4,z5,z6]),(0,[z1,z151,z2,z3,z4,z5,z135]),(0,[z1,z314,z2,z3,z4,z5,z6]),(0,[z315,z1,z2,z3,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z316])],[(0,[z1,z317,z2,z3,z4,z5,z6]),(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z117,z22]),(0,[z1,z319,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z320,z5,z6]),(0,[z1,z321,z2,z95,z4,z5,z6]),(0,[z1,z322,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z193,z6]),(0,[z1,z2,z3,z4,z5,z6,z323]),(0,[z1,z2,z324,z3,z4,z5,z6])],[(1,[z1,z2,z49,z4,z5,z6]),(0,[z1,z2,z36,z3,z133,z5,z6]),(0,[z1,z325,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z326,z6]),(0,[z1,z2,z3,z4,z5,z6,z327]),(0,[z1,z328,z2,z3,z4,z5,z6])],[(0,[z1,z2,z329,z3,z4,z5,z6]),(0,[z80,z1,z2,z3,z4,z5,z121])],[(0,[z42,z2,z137,z3,z4,z5,z6]),(1,[z132,z2,z3,z133,z5,z6]),(0,[z1,z321,z2,z3,z4,z177,z6]),(0,[z1,z330,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z331,z6]),(0,[z1,z98,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z209,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z221,z21]),(0,[z1,z119,z2,z3,z4,z91,z6]),(0,[z1,z332,z2,z3,z4,z5,z6])],[(0,[z1,z333,z2,z3,z4,z5,z6]),(0,[z334,z1,z2,z3,z4,z5,z6]),(0,[z80,z1,z2,z65,z4,z5,z6]),(0,[z1,z2,z3,z335,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z336,z6]),(1,[z1,z2,z3,z4,z5,z309]),(0,[z1,z337,z2,z3,z4,z5,z6])],[(0,[z1,z338,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z187,z133,z5,z6]),(0,[z1,z339,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z340,z6]),(0,[z1,z2,z25,z3,z4,z5,z193]),(0,[z1,z2,z3,z4,z5,z341,z6]),(0,[z1,z2,z3,z104,z120,z5,z6])],[(0,[z342,z1,z73,z2,z3,z4,z6]),(0,[z1,z146,z2,z3,z4,z5,z22])],[(0,[z1,z2,z3,z343,z4,z5,z6]),(0,[z1,z2,z3,z4,z55,z5,z6])],[(1,[z1,z94,z2,z3,z5,z6]),(0,[z1,z2,z3,z227,z4,z5,z6]),(0,[z1,z151,z2,z3,z207,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z250])],[(0,[z1,z344,z2,z3,z4,z5,z6]),(0,[z1,z24,z2,z3,z169,z5,z6])],[(0,[z1,z2,z3,z345,z4,z5,z6]),(0,[z140,z2,z3,z4,z5,z91,z6]),(0,[z1,z2,z3,z4,z346,z5,z6]),(0,[z1,z2,z3,z4,z257,z5,z6]),(0,[z1,z347,z2,z3,z4,z5,z6]),(1,[z1,z2,z25,z4,z5,z193]),(0,[z1,z348,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z104,z120,z6]),(0,[z1,z24,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z349])]],
   [[(0,[z0,z1,z16,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z350,z5,z6])],[(0,[z42,z2,z3,z4,z17,z5,z6]),(0,[z1,z321,z64,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z351,z6]),(0,[z1,z2,z3,z4,z5,z6,z352])],[(0,[z1,z2,z353,z3,z4,z5,z6]),(0,[z1,z354,z2,z3,z4,z5,z6]),(0,[z208,z1,z2,z3,z4,z5,z216]),(1,[z1,z2,z3,z355,z5,z6]),(0,[z1,z2,z3,z4,z5,z356,z6])],[(0,[z1,z2,z3,z357,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z358,z6]),(0,[z1,z73,z2,z3,z4,z203,z6]),(0,[z359,z1,z2,z3,z4,z5,z6])],[(0,[z1,z360,z2,z3,z4,z5,z6]),(0,[z1,z103,z2,z3,z5,z179,z6])],[(1,[z1,z2,z3,z245,z5,z6]),(0,[z1,z2,z25,z3,z4,z5,z21]),(1,[z1,z2,z3,z4,z361,z6]),(0,[z1,z2,z3,z120,z5,z170,z6]),(1,[z1,z237,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z362,z6])],[(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z363]),(0,[z1,z192,z2,z95,z4,z5,z6]),(0,[z1,z364,z2,z3,z4,z5,z6])],[(0,[z0,z1,z137,z3,z4,z5,z6]),(0,[z1,z2,z81,z37,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z264])]],
   [[(0,[z1,z365,z2,z3,z4,z5,z6]),(0,[z1,z366,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z5,z6])],[(0,[z1,z367,z2,z3,z4,z5,z6]),(0,[z1,z2,z368,z3,z4,z5,z6]),(0,[z1,z2,z369,z3,z4,z5,z6]),(0,[z370,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z371,z6]),(0,[z1,z2,z3,z4,z372,z5,z6]),(0,[z1,z2,z3,z4,z99,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z373]),(0,[z1,z2,z3,z4,z5,z374,z6]),(0,[z1,z375,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z258])],[(0,[z376,z1,z2,z3,z4,z5,z6]),(0,[z377,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z378,z4,z5,z6]),(0,[z1,z2,z3,z4,z100,z6,z198])],[(0,[z1,z379,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z267,z5,z6]),(0,[z1,z2,z3,z4,z5,z380,z6]),(0,[z1,z2,z3,z4,z5,z6,z381]),(0,[z1,z2,z3,z4,z99,z5,z198])],[(0,[z1,z382,z2,z3,z4,z5,z6]),(0,[z1,z54,z3,z4,z55,z5,z6]),(0,[z1,z2,z3,z383,z4,z5,z6])],[(0,[z1,z2,z65,z37,z4,z5,z6]),(0,[z1,z2,z384,z3,z4,z5,z6]),(0,[z1,z2,z3,z385,z4,z5,z6]),(0,[z1,z2,z3,z169,z4,z5,z117])],[(0,[z1,z2,z3,z4,z5,z90,z6]),(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z65,z4,z5,z74,z6]),(0,[z80,z1,z2,z81,z4,z5,z6]),(0,[z132,z1,z2,z3,z76,z5,z6]),(0,[z1,z2,z3,z104,z76,z5,z6]),(0,[z208,z1,z2,z387,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z388,z6]),(0,[z389,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z169,z5,z170,z6])]],
   [[(0,[z1,z2,z3,z4,z390,z5,z6]),(0,[z1,z2,z391,z3,z4,z5,z6]),(0,[z392,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z76,z4,z133,z5,z6]),(0,[z342,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z393,z4,z5,z6]),(0,[z1,z192,z321,z3,z4,z5,z6]),(0,[z1,z321,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z394,z6]),(1,[z140,z2,z3,z4,z5,z6]),(0,[z1,z73,z12,z2,z4,z5,z6]),(1,[z1,z2,z3,z4,z167,z5]),(0,[z1,z395,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z179])],[(0,[z1,z2,z3,z4,z5,z396,z6]),(0,[z1,z2,z65,z95,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z121]),(0,[z1,z2,z3,z4,z5,z397,z6])],[(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z399,z2,z3,z4,z5,z6]),(0,[z208,z1,z2,z400,z4,z5,z6]),(0,[z1,z2,z3,z169,z4,z5,z221])],[(0,[z1,z88,z3,z4,z5,z221,z6])],[(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z402,z5,z6]),(0,[z1,z2,z403,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z404,z5,z6]),(0,[z1,z405,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z406,z6]),(0,[z1,z2,z3,z4,z5,z204,z6]),(0,[z1,z2,z3,z407,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z408]),(0,[z1,z151,z2,z3,z187,z5,z6]),(0,[z1,z2,z37,z4,z203,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z409])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z410]),(0,[z1,z73,z2,z3,z4,z55,z6])],[(0,[z1,z2,z411,z3,z4,z5,z6]),(0,[z412,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z413]),(0,[z1,z88,z146,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z414,z6])],[(0,[z208,z1,z73,z2,z3,z4,z6]),(0,[z1,z2,z36,z3,z37,z5,z6]),(0,[z1,z2,z3,z415,z4,z5,z6])],[(0,[z416,z1,z2,z3,z4,z5,z6]),(0,[z77,z1,z2,z3,z4,z5,z6]),(0,[z1,z151,z3,z187,z4,z5,z6]),(0,[z1,z2,z3,z417,z4,z5,z6]),(0,[z1,z2,z418,z3,z4,z5,z6])],[(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z193,z6,z59]),(0,[z1,z75,z2,z3,z4,z5,z179])],[(0,[z1,z2,z3,z4,z5,z420,z6])],[(0,[z1,z2,z3,z133,z5,z170,z6]),(0,[z1,z58,z2,z4,z203,z5,z6]),(0,[z1,z197,z2,z3,z4,z99,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z421,z6]),(0,[z1,z2,z3,z422,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z423])],[(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z425,z4,z5,z6]),(0,[z1,z426,z2,z3,z4,z5,z6])],[(0,[z1,z139,z2,z3,z65,z4,z6]),(0,[z1,z2,z3,z4,z5,z427,z6]),(0,[z1,z192,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z55,z5,z91,z6]),(0,[z1,z2,z428,z3,z4,z5,z6])],[(0,[z1,z429,z2,z3,z4,z5,z6]),(0,[z430,z1,z2,z3,z4,z5,z6]),(0,[z1,z431,z2,z3,z4,z5,z6]),(0,[z1,z197,z2,z3,z4,z6,z198])],[(0,[z1,z2,z3,z4,z432,z5,z6]),(0,[z1,z2,z3,z4,z5,z433,z6]),(0,[z1,z2,z3,z4,z55,z204,z6])],[(0,[z42,z1,z2,z3,z434,z5,z6]),(0,[z1,z2,z3,z400,z4,z5,z6]),(0,[z1,z73,z2,z4,z5,z74,z6]),(0,[z1,z2,z3,z4,z435,z5,z6]),(0,[z1,z2,z436,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z43,z6]),(0,[z1,z2,z3,z437,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z438,z6]),(0,[z1,z2,z3,z4,z439,z5,z6]),(0,[z1,z2,z3,z4,z120,z5,z6]),(0,[z1,z2,z3,z4,z440,z5,z6])],[(0,[z42,z1,z2,z3,z4,z90,z6]),(0,[z1,z2,z3,z4,z441,z5,z6]),(0,[z1,z442,z2,z3,z4,z5,z6]),(0,[z1,z2,z443,z3,z4,z5,z6]),(0,[z1,z12,z2,z4,z203,z5,z6]),(0,[z1,z2,z3,z4,z444,z5,z6])]],
   [[(0,[z1,z2,z445,z3,z4,z5,z6]),(0,[z1,z73,z2,z95,z4,z5,z6]),(0,[z1,z260,z2,z3,z95,z4,z5]),(0,[z2,z3,z4,z5,z281,z91,z6]),(0,[z1,z446,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z203,z5,z193,z6]),(0,[z1,z2,z447,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z100,z6]),(0,[z448,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z449,z5,z6]),(0,[z77,z1,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z4,z207,z5,z6])],[(0,[z1,z450,z2,z3,z4,z5,z6]),(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z1,z452,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z453,z5,z6])],[(0,[z1,z106,z2,z3,z207,z5,z6]),(0,[z1,z2,z3,z454,z4,z5,z6]),(1,[z1,z2,z3,z4,z99,z100])],[(0,[z1,z455,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z17,z91,z6])],[(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z1,z2,z456,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z216]),(0,[z27,z1,z2,z3,z355,z5,z6]),(0,[z1,z54,z2,z422,z4,z5,z6])],[(0,[z1,z2,z3,z4,z267,z5,z6]),(0,[z1,z2,z3,z4,z457,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z117]),(0,[z1,z458,z2,z3,z4,z5,z6]),(1,[z1,z2,z28,z4,z5,z6]),(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z460,z3,z4,z5,z6]),(0,[z1,z163,z2,z3,z4,z5,z6]),(0,[z461,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z208,z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z167,z5,z6]),(0,[z462,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z463,z6]),(0,[z1,z2,z3,z4,z5,z6,z464]),(0,[z1,z2,z3,z4,z5,z6,z198])],[(0,[z465,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z466]),(0,[z1,z467,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z468,z5,z6]),(0,[z1,z58,z2,z3,z169,z4,z5]),(0,[z1,z2,z3,z4,z469,z5,z6])],[(0,[z42,z208,z2,z3,z4,z5,z6]),(0,[z470,z1,z2,z3,z4,z5,z6])],[(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z91,z6])],[(0,[z1,z24,z2,z3,z133,z5,z6]),(0,[z1,z472,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z76,z5,z170,z6])],[(0,[z1,z2,z3,z76,z5,z179,z6]),(0,[z1,z2,z3,z355,z4,z5,z6]),(0,[z1,z473,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z474,z6]),(0,[z1,z2,z3,z4,z5,z6,z475])],[(0,[z1,z2,z3,z4,z5,z476,z6]),(0,[z1,z2,z477,z3,z4,z5,z6]),(0,[z1,z123,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z478,z6]),(1,[z1,z2,z200,z4,z5,z6]),(0,[z1,z2,z95,z4,z203,z5,z6]),(0,[z1,z24,z2,z36,z3,z5,z6]),(0,[z1,z479,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z186]),(0,[z1,z480,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z481,z6]),(0,[z1,z2,z3,z4,z5,z6,z482])],[(0,[z1,z2,z3,z4,z5,z483,z6]),(0,[z1,z2,z3,z4,z5,z6,z7]),(0,[z342,z2,z3,z4,z17,z5,z6]),(1,[z1,z2,z422,z4,z5,z6]),(0,[z484,z1,z2,z3,z4,z5,z6])],[(0,[z42,z1,z2,z3,z171,z5,z6]),(0,[z1,z2,z485,z3,z4,z5,z6]),(1,[z1,z2,z387,z4,z5,z6]),(0,[z1,z486,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z179,z6]),(0,[z1,z24,z2,z3,z4,z5,z170])],[(0,[z1,z2,z3,z4,z5,z117,z198]),(0,[z487,z1,z2,z3,z4,z5,z6]),(0,[z488,z1,z2,z3,z4,z5,z6]),(1,[z1,z24,z2,z3,z5,z258])],[(0,[z1,z2,z3,z4,z489,z5,z6]),(0,[z1,z12,z2,z3,z133,z5,z6]),(0,[z1,z2,z3,z169,z4,z5,z22])],[(0,[z1,z2,z3,z207,z5,z170,z6]),(0,[z1,z54,z119,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z490])],[(0,[z491,z1,z2,z3,z4,z5,z6]),(0,[z80,z1,z2,z3,z492,z5,z6]),(0,[z1,z493,z2,z3,z4,z5,z6]),(0,[z342,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z400,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z494,z6]),(1,[z1,z2,z3,z61,z5,z6]),(0,[z1,z2,z3,z495,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z496,z6]),(0,[z1,z2,z3,z4,z497,z5,z6]),(0,[z1,z498,z2,z3,z4,z5,z6]),(0,[z499,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z500,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z13,z5,z6]),(0,[z501,z1,z2,z3,z4,z5,z6])],[(0,[z77,z1,z2,z3,z4,z5,z105]),(0,[z1,z2,z3,z4,z5,z6,z502]),(0,[z1,z146,z2,z3,z4,z5,z6]),(0,[z1,z58,z146,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z503,z5,z6]),(0,[z1,z2,z3,z4,z504,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z33]),(0,[z27,z1,z2,z3,z4,z5,z117]),(0,[z1,z88,z2,z3,z257,z5,z6]),(0,[z1,z505,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z506,z5,z6]),(0,[z1,z2,z3,z507,z4,z5,z6]),(0,[z1,z2,z3,z4,z99,z100,z6])],[(0,[z508,z1,z2,z3,z4,z5,z6]),(0,[z1,z73,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z227,z5,z6]),(0,[z1,z106,z2,z3,z187,z5,z6]),(0,[z1,z2,z3,z509,z4,z5,z6]),(0,[z1,z2,z3,z4,z510,z5,z6])],[(0,[z342,z1,z2,z83,z3,z4,z6]),(0,[z1,z2,z3,z511,z4,z5,z6]),(0,[z1,z103,z2,z3,z5,z170,z6]),(0,[z1,z24,z2,z3,z4,z99,z5])],[(0,[z1,z58,z2,z65,z4,z5,z6]),(0,[z512,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z513,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z514,z6]),(0,[z1,z2,z3,z4,z5,z515,z6]),(0,[z1,z2,z3,z516,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z517,z4,z5,z6]),(0,[z1,z58,z2,z3,z4,z5,z117]),(0,[z518,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z519,z4,z5,z6])],[(0,[z1,z2,z3,z245,z4,z5,z6]),(0,[z1,z2,z3,z520,z4,z5,z6])],[(0,[z42,z1,z2,z124,z4,z5,z6]),(0,[z1,z321,z2,z64,z4,z5,z6])],[(1,[z342,z2,z3,z4,z17,z6]),(0,[z521,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z522,z6])],[(0,[z1,z192,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z523,z5,z6])],[(0,[z1,z2,z36,z3,z76,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z524]),(0,[z1,z2,z83,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z525])],[(0,[z208,z342,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z21]),(0,[z1,z2,z3,z4,z5,z6,z526]),(0,[z1,z527,z2,z3,z4,z5,z6])],[(0,[z1,z12,z2,z65,z4,z5,z6]),(0,[z1,z528,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z246,z4,z5]),(0,[z1,z2,z83,z3,z4,z91,z6]),(0,[z1,z2,z3,z4,z5,z529,z6])]],
   [[(0,[z1,z530,z2,z3,z4,z5,z6]),(0,[z1,z531,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z532]),(0,[z1,z533,z2,z3,z4,z5,z6]),(0,[z1,z2,z534,z3,z4,z5,z6])],[(0,[z77,z1,z2,z3,z133,z5,z6]),(1,[z1,z260,z2,z3,z4,z5]),(0,[z1,z2,z3,z37,z4,z5,z6])],[(0,[z1,z2,z3,z187,z76,z5,z6]),(0,[z1,z535,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z536]),(0,[z1,z2,z36,z3,z13,z5,z6]),(0,[z1,z2,z3,z4,z5,z74,z6])],[(0,[z1,z2,z537,z3,z4,z5,z6]),(0,[z77,z132,z2,z3,z4,z5,z6]),(0,[z538,z1,z2,z3,z4,z5,z6]),(0,[z1,z54,z2,z3,z4,z55,z6]),(0,[z1,z2,z539,z3,z4,z5,z6])],[(0,[z1,z2,z3,z540,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z541]),(0,[z1,z2,z3,z4,z542,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z543])],[(0,[z208,z1,z2,z3,z4,z5,z406]),(0,[z1,z2,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z6]),(0,[z1,z2,z3,z4,z5,z6,z544]),(0,[z1,z197,z2,z3,z169,z4,z5])],[(0,[z1,z2,z3,z4,z545,z5,z6]),(0,[z1,z2,z3,z546,z4,z5,z6])],[(0,[z547,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z548,z1,z2,z3,z4,z5,z6]),(0,[z1,z549,z2,z3,z4,z5,z6]),(1,[z1,z106,z3,z207,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z59]),(0,[z1,z2,z3,z4,z5,z6,z550])],[(1,[z42,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z551,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z135])],[(0,[z552,z1,z2,z3,z4,z5,z6]),(0,[z208,z16,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z553,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z554,z6]),(0,[z1,z2,z3,z4,z5,z6,z555]),(0,[z1,z2,z3,z4,z5,z556,z6])],[(1,[z1,z2,z3,z492,z5,z6]),(0,[z1,z2,z3,z4,z5,z557,z6]),(0,[z1,z2,z25,z3,z4,z5,z6]),(0,[z1,z24,z2,z3,z5,z6,z258]),(0,[z1,z237,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z558,z5,z6])],[(0,[z1,z2,z3,z4,z5,z559,z6]),(0,[z208,z1,z560,z3,z4,z5,z6]),(0,[z1,z192,z2,z64,z4,z5,z6]),(0,[z1,z2,z3,z561,z4,z5,z6]),(0,[z1,z562,z2,z3,z4,z5,z6]),(0,[z1,z58,z2,z3,z4,z5,z193]),(0,[z1,z2,z4,z5,z563,z179,z6])],[(0,[z1,z58,z2,z81,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z1,z2,z565,z3,z4,z5,z6])],[(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z33]),(0,[z567,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z568,z4,z5,z6]),(0,[z1,z2,z3,z569,z4,z5,z6]),(1,[z1,z155,z2,z4,z5,z6])],[(0,[z208,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z570,z6]),(0,[z1,z2,z3,z4,z5,z571,z6]),(0,[z1,z2,z64,z3,z4,z5,z6]),(0,[z1,z2,z572,z3,z4,z5,z6]),(0,[z573,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z574,z6]),(0,[z1,z2,z3,z4,z5,z563,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z575]),(0,[z80,z1,z2,z3,z4,z5,z186]),(1,[z1,z2,z511,z4,z5,z6]),(0,[z1,z2,z3,z4,z576,z5,z6]),(0,[z1,z2,z3,z4,z577,z5,z6]),(0,[z1,z2,z3,z169,z4,z5,z258])],[(0,[z27,z1,z2,z3,z4,z5,z21]),(0,[z1,z106,z151,z3,z4,z5,z6]),(0,[z1,z75,z2,z3,z4,z5,z6])],[(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z214,z6]),(0,[z1,z2,z579,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z580,z5,z6]),(0,[z581,z1,z2,z3,z4,z5,z6]),(0,[z1,z582,z2,z3,z4,z5,z6]),(0,[z1,z583,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z584])],[(0,[z1,z12,z2,z3,z37,z5,z6])],[(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z586,z4,z5,z6]),(1,[z1,z103,z2,z3,z179,z6])],[(0,[z1,z2,z3,z4,z5,z587,z6]),(0,[z1,z12,z2,z81,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z588,z6]),(0,[z1,z589,z2,z3,z4,z5,z6])],[(0,[z208,z1,z2,z83,z3,z4,z6]),(0,[z1,z2,z3,z4,z590,z5,z6])],[(1,[z1,z2,z3,z434,z5,z6]),(0,[z1,z2,z81,z4,z5,z193,z6]),(0,[z342,z1,z2,z3,z4,z204,z6]),(0,[z1,z2,z3,z4,z5,z591,z6]),(0,[z1,z58,z2,z3,z4,z5,z21]),(0,[z1,z73,z2,z37,z4,z5,z6])]],
   [[(1,[z1,z2,z9,z3,z4,z6]),(0,[z1,z2,z3,z4,z592,z5,z6]),(0,[z1,z2,z3,z4,z5,z361,z6]),(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z594,z6]),(0,[z1,z2,z3,z4,z595,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z596])],[(0,[z1,z2,z3,z597,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z598,z6]),(0,[z1,z599,z2,z3,z4,z5,z6]),(0,[z1,z600,z2,z3,z4,z5,z6])],[],[(0,[z77,z1,z2,z172,z4,z5,z6]),(0,[z1,z106,z3,z4,z207,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6]),(0,[z1,z2,z3,z4,z5,z602,z6]),(0,[z603,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z604,z4,z5,z6])],[(0,[z1,z2,z83,z4,z203,z5,z6]),(0,[z1,z2,z3,z4,z605,z5,z6])],[(0,[z1,z2,z3,z4,z606,z5,z6]),(0,[z1,z2,z3,z262,z4,z5,z6]),(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z264,z198])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z608,z2,z3,z4,z5,z6]),(0,[z1,z609,z2,z3,z4,z5,z6]),(0,[z1,z2,z65,z4,z5,z193,z6]),(0,[z610,z1,z2,z3,z4,z5,z6]),(1,[z1,z146,z3,z4,z5,z22])],[(0,[z611,z1,z2,z3,z4,z5,z6]),(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z613,z2,z3,z4,z5,z6]),(0,[z1,z2,z614,z3,z4,z5,z6]),(0,[z1,z615,z2,z3,z4,z5,z6])]],
   [[(0,[z42,z1,z2,z49,z4,z5,z6]),(0,[z1,z616,z2,z3,z4,z5,z6]),(0,[z1,z2,z617,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z618,z5,z6]),(0,[z57,z2,z3,z4,z5,z6,z117]),(1,[z1,z321,z64,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z27,z57,z2,z3,z4,z5,z6])],[(0,[z1,z2,z387,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z619]),(1,[z1,z2,z3,z4,z177,z6])],[(0,[z1,z620,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z621,z5,z6]),(0,[z1,z622,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z623]),(0,[z1,z2,z3,z4,z5,z6,z624])],[(0,[z1,z625,z2,z3,z4,z5,z6]),(0,[z1,z2,z626,z3,z4,z5,z6])],[(0,[z1,z2,z3,z627,z4,z5,z6])],[(0,[z138,z1,z2,z65,z4,z5,z6]),(1,[z77,z2,z3,z76,z5,z6]),(0,[z628,z1,z2,z3,z4,z5,z6]),(0,[z1,z73,z58,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z629,z5,z6]),(0,[z1,z2,z3,z4,z630,z5,z6]),(0,[z1,z2,z3,z4,z631,z5,z6]),(0,[z1,z2,z632,z3,z4,z5,z6]),(0,[z1,z633,z2,z3,z4,z5,z6]),(0,[z1,z103,z2,z3,z4,z5,z6]),(0,[z1,z24,z2,z3,z120,z5,z6]),(0,[z1,z634,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z635,z6]),(0,[z1,z2,z3,z4,z5,z6,z636]),(0,[z1,z637,z2,z3,z4,z5,z6]),(0,[z1,z119,z3,z4,z5,z91,z6]),(1,[z1,z2,z3,z262,z5,z6]),(0,[z1,z58,z88,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z638]),(0,[z1,z2,z3,z4,z639,z5,z6])],[(0,[z132,z2,z3,z4,z133,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z640]),(0,[z1,z2,z3,z4,z641,z5,z6]),(1,[z1,z2,z4,z5,z563,z6]),(0,[z1,z98,z2,z3,z5,z6,z198])],[(0,[z1,z24,z2,z3,z207,z5,z6])],[(0,[z1,z642,z2,z3,z4,z5,z6]),(0,[z643,z1,z2,z3,z4,z5,z6])],[(0,[z1,z644,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z645,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z646])],[(0,[z1,z2,z3,z4,z647,z5,z6]),(0,[z1,z2,z3,z4,z5,z170,z6]),(0,[z1,z2,z3,z5,z170,z6,z258])],[(0,[z1,z2,z3,z4,z492,z5,z6]),(0,[z1,z73,z2,z64,z4,z5,z6]),(0,[z1,z2,z64,z4,z203,z5,z6]),(0,[z1,z648,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z649,z6])],[(0,[z1,z2,z3,z4,z5,z309,z6]),(0,[z1,z54,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z650,z6]),(0,[z1,z651,z2,z3,z4,z5,z6]),(0,[z1,z652,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z653,z2,z3,z4,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z655,z5,z6]),(0,[z1,z656,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z657]),(0,[z1,z2,z3,z4,z658,z5,z6])],[(1,[z1,z2,z3,z4,z5,z406]),(0,[z1,z2,z3,z4,z659,z5,z6]),(0,[z1,z54,z2,z3,z4,z91,z6]),(0,[z1,z88,z2,z3,z4,z5,z221]),(0,[z1,z660,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z434,z4,z5,z6]),(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z661,z6]),(0,[z1,z151,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z281,z6]),(0,[z1,z2,z3,z104,z4,z5,z6]),(0,[z1,z2,z3,z4,z662,z5,z6])],[(0,[z663,z1,z2,z3,z4,z5,z6]),(0,[z664,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z169,z4,z5,z6])],[(1,[z1,z2,z3,z86,z5,z6]),(0,[z1,z2,z3,z4,z665,z5,z6]),(0,[z1,z560,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z666,z6])],[(0,[z667,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z668,z5,z6]),(0,[z1,z155,z2,z4,z5,z179,z6]),(0,[z1,z24,z197,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z669,z6]),(0,[z1,z2,z4,z203,z5,z74,z6]),(0,[z1,z2,z25,z3,z4,z5,z59]),(0,[z1,z197,z2,z3,z4,z5,z100])],[(0,[z208,z1,z2,z3,z4,z204,z6]),(0,[z1,z119,z2,z3,z4,z55,z6]),(0,[z1,z2,z3,z4,z5,z6,z670])]],
   [[(1,[z1,z560,z3,z4,z5,z6]),(0,[z1,z2,z3,z671,z4,z5,z6]),(0,[z1,z2,z3,z672,z4,z5,z6]),(0,[z1,z673,z2,z3,z4,z5,z6])],[(0,[z2,z81,z3,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z105,z6]),(0,[z208,z2,z3,z4,z5,z204,z6]),(0,[z1,z73,z2,z3,z4,z91,z6]),(0,[z1,z2,z3,z4,z5,z674,z6]),(1,[z1,z2,z36,z37,z5,z6]),(0,[z1,z2,z3,z675,z4,z5,z6])],[(0,[z1,z24,z2,z3,z4,z5,z117]),(0,[z1,z321,z2,z3,z4,z361,z6]),(0,[z1,z2,z3,z676,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z677,z2,z3,z4,z5,z6]),(0,[z1,z24,z103,z2,z3,z5,z6])],[(1,[z1,z2,z124,z4,z5,z6]),(0,[z138,z1,z2,z81,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z678,z6]),(0,[z1,z2,z3,z4,z5,z6,z679]),(0,[z1,z24,z2,z3,z76,z5,z6]),(0,[z27,z1,z2,z511,z4,z5,z6]),(0,[z1,z680,z2,z3,z4,z5,z6]),(0,[z1,z2,z25,z3,z169,z4,z5])],[(0,[z42,z1,z2,z3,z4,z5,z214]),(0,[z1,z2,z3,z4,z5,z681,z6]),(0,[z1,z682,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z683]),(1,[z57,z2,z3,z4,z5,z117])],[(0,[z1,z2,z3,z246,z4,z5,z6]),(0,[z1,z88,z2,z25,z3,z4,z5]),(1,[z1,z163,z2,z3,z4,z5]),(0,[z684,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z685]),(0,[z686,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z200,z3,z4,z5,z6]),(1,[z1,z119,z3,z4,z91,z6]),(0,[z1,z24,z2,z3,z4,z5,z221]),(0,[z1,z2,z36,z3,z5,z170,z6]),(0,[z687,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z689,z6]),(0,[z1,z2,z3,z4,z690,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z691])],[(0,[z16,z2,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z221,z6]),(0,[z1,z2,z3,z4,z5,z692,z6])],[(1,[z1,z2,z83,z4,z203,z6]),(0,[z1,z58,z2,z25,z4,z5,z6])],[(0,[z0,z16,z2,z3,z4,z5,z6]),(0,[z693,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z187,z4,z207,z5,z6]),(0,[z694,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z695,z6]),(0,[z696,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z697,z5,z6])],[(0,[z1,z2,z83,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z698,z6]),(0,[z1,z24,z2,z3,z187,z5,z6]),(0,[z1,z2,z3,z187,z5,z170,z6]),(0,[z1,z699,z2,z3,z4,z5,z6])],[(0,[z1,z12,z2,z3,z76,z5,z6]),(0,[z1,z2,z700,z3,z4,z5,z6])],[(0,[z1,z701,z2,z3,z4,z5,z6]),(0,[z77,z2,z3,z76,z4,z5,z6]),(1,[z27,z2,z3,z4,z5,z21]),(0,[z702,z1,z2,z3,z4,z5,z6]),(0,[z1,z703,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z704,z6])],[(0,[z1,z2,z3,z4,z705,z5,z6]),(0,[z1,z2,z3,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z707,z2,z3,z4,z5]),(0,[z708,z2,z3,z4,z5,z6]),(0,[z1,z24,z2,z178,z3,z5]),(0,[z1,z237,z98,z2,z5,z6])],[(0,[z1,z209,z3,z245,z5,z6]),(0,[z1,z2,z387,z245,z5,z6]),(0,[z1,z2,z3,z709,z5,z6]),(0,[z1,z2,z4,z5,z6,z710])],[(0,[z573,z2,z81,z4,z5,z6]),(0,[z342,z2,z3,z4,z711,z6]),(0,[z2,z3,z4,z5,z21,z712]),(0,[z140,z2,z3,z713,z5,z6]),(0,[z1,z2,z3,z5,z170,z714])],[(0,[z1,z2,z3,z715,z5,z6]),(0,[z1,z2,z3,z4,z5,z716])],[(0,[z1,z2,z3,z717,z5,z6]),(0,[z1,z139,z2,z3,z4,z6]),(0,[z1,z718,z3,z4,z5,z6]),(0,[z1,z106,z428,z3,z5,z6])],[(0,[z1,z2,z3,z4,z719,z6]),(0,[z77,z2,z3,z76,z5,z6]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z1,z2,z400,z245,z5,z6]),(0,[z721,z2,z3,z4,z5,z6])],[(0,[z1,z12,z2,z390,z5,z6]),(0,[z1,z12,z163,z2,z3,z5])],[(0,[z1,z2,z3,z722,z5,z6]),(0,[z1,z2,z3,z262,z5,z6]),(0,[z1,z2,z3,z4,z5,z723]),(0,[z1,z2,z3,z724,z5,z6]),(0,[z1,z75,z2,z3,z120,z5]),(0,[z1,z24,z2,z3,z5,z714])]],
   [[(0,[z140,z16,z3,z4,z5,z6]),(0,[z1,z2,z387,z267,z5,z6]),(0,[z1,z2,z4,z5,z563,z6])],[(0,[z80,z2,z81,z492,z5,z6]),(0,[z1,z2,z3,z335,z5,z170]),(0,[z1,z2,z3,z4,z5,z725]),(0,[z1,z2,z3,z5,z726,z6]),(0,[z1,z727,z2,z4,z5,z6])],[(0,[z241,z2,z81,z4,z5,z6]),(0,[z1,z728,z3,z4,z5,z6]),(0,[z208,z56,z2,z3,z4,z6]),(1,[z1,z2,z724,z5,z6])],[(0,[z1,z2,z3,z434,z5,z33]),(0,[z1,z2,z729,z4,z5,z6]),(0,[z1,z2,z3,z4,z730,z6]),(0,[z1,z2,z3,z731,z5,z6]),(0,[z547,z2,z65,z4,z5,z6])],[(0,[z1,z2,z3,z171,z5,z6]),(0,[z1,z139,z2,z37,z4,z6]),(0,[z1,z2,z400,z267,z5,z6]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z1,z2,z3,z4,z732,z6]),(0,[z1,z163,z2,z36,z3,z5]),(0,[z1,z2,z3,z169,z469,z5])],[(0,[z1,z2,z3,z4,z5,z733]),(0,[z1,z2,z3,z4,z5,z734]),(0,[z1,z560,z3,z4,z5,z406]),(0,[z140,z2,z735,z4,z5,z6])],[(0,[z1,z2,z3,z736,z5,z6]),(0,[z1,z2,z737,z4,z5,z6]),(0,[z2,z3,z4,z17,z711,z6]),(0,[z1,z2,z738,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z739])],[(0,[z140,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z740]),(0,[z1,z2,z65,z4,z5,z186]),(0,[z1,z2,z3,z741,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z742]),(0,[z1,z2,z3,z4,z743,z6]),(0,[z16,z3,z4,z5,z598,z6]),(0,[z1,z2,z3,z744,z5,z6]),(0,[z1,z2,z3,z4,z745,z6])],[(0,[z2,z3,z4,z5,z281,z6]),(0,[z1,z2,z200,z76,z5,z6]),(0,[z1,z325,z3,z4,z5,z22])],[(0,[z77,z2,z3,z76,z5,z7]),(0,[z1,z2,z3,z4,z5,z746]),(0,[z1,z2,z3,z169,z5,z170])],[(0,[z1,z2,z3,z86,z5,z6]),(0,[z1,z3,z4,z5,z6,z747]),(0,[z2,z3,z76,z748,z5,z6]),(0,[z1,z2,z3,z4,z711,z6])],[(1,[z749,z3,z4,z5,z6]),(0,[z1,z2,z750,z4,z5,z6]),(0,[z1,z2,z25,z144,z4,z5])],[(0,[z1,z2,z3,z751,z5,z6]),(0,[z2,z3,z4,z5,z711,z6])],[(0,[z1,z2,z3,z5,z6,z752]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z1,z3,z4,z754,z5,z6])],[(0,[z1,z2,z3,z434,z90,z6]),(0,[z1,z560,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z755,z6])]],
   [[(0,[z1,z2,z3,z4,z756,z6]),(0,[z1,z2,z36,z37,z5,z6])],[(0,[z1,z2,z3,z757,z5,z6]),(0,[z1,z2,z4,z203,z758,z6])],[(0,[z1,z2,z3,z5,z6,z759])],[(0,[z1,z2,z124,z4,z5,z6]),(0,[z1,z379,z3,z4,z91,z6]),(0,[z1,z12,z2,z595,z5,z6]),(0,[z1,z2,z3,z760,z5,z6])],[(0,[z2,z3,z4,z5,z712,z6])],[(0,[z1,z2,z761,z4,z5,z6]),(0,[z1,z151,z3,z187,z5,z6]),(0,[z1,z2,z3,z187,z5,z309]),(1,[z1,z3,z4,z754,z6])],[(0,[z1,z94,z260,z2,z3,z5])],[(0,[z1,z2,z49,z4,z43,z6]),(0,[z1,z2,z762,z4,z5,z6]),(0,[z1,z237,z2,z4,z5,z117]),(0,[z1,z2,z5,z6,z10,z264])]],
   [[(0,[z1,z2,z3,z763,z4,z5]),(0,[z1,z2,z3,z764,z5,z6]),(0,[z1,z94,z2,z65,z5,z6]),(0,[z1,z2,z353,z4,z5,z193]),(0,[z1,z2,z3,z4,z5,z765]),(0,[z1,z2,z3,z766,z5,z6])],[(0,[z1,z767,z2,z3,z4,z5]),(0,[z208,z2,z3,z4,z204,z406]),(0,[z1,z2,z3,z4,z5,z768])],[(0,[z1,z314,z3,z4,z91,z6])],[(0,[z1,z139,z12,z2,z4,z6]),(0,[z1,z75,z2,z3,z76,z5]),(0,[z1,z2,z511,z355,z5,z6])],[(0,[z208,z2,z3,z4,z90,z6]),(0,[z1,z769,z3,z4,z5,z6]),(0,[z1,z770,z2,z3,z4,z6]),(0,[z1,z771,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z193,z772])],[(0,[z749,z137,z3,z4,z5,z6]),(0,[z1,z773,z3,z4,z5,z6]),(0,[z1,z2,z81,z4,z5,z186]),(0,[z1,z2,z774,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z2,z172,z4,z5,z6]),(0,[z119,z3,z4,z281,z91,z6]),(0,[z1,z2,z3,z5,z6,z250]),(0,[z1,z2,z3,z4,z5,z776])],[(0,[z1,z2,z3,z5,z6,z777]),(0,[z1,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z5,z714,z258])]],
   [[(0,[z1,z778,z3,z4,z5,z6])],[],[(0,[z80,z2,z81,z4,z5,z186]),(0,[z77,z2,z3,z76,z5,z105]),(0,[z1,z209,z3,z4,z5,z216]),(0,[z1,z192,z260,z95,z4,z5]),(0,[z140,z2,z3,z4,z5,z779]),(0,[z1,z2,z3,z5,z780,z6]),(0,[z1,z24,z2,z63,z3,z5])],[(0,[z581,z2,z81,z4,z5,z6]),(0,[z208,z2,z3,z4,z204,z6]),(0,[z1,z2,z4,z5,z781,z6]),(0,[z1,z2,z3,z246,z227,z5])],[(0,[z42,z137,z3,z4,z5,z214]),(0,[z1,z782,z2,z3,z4,z5]),(0,[z1,z431,z3,z187,z5,z6])],[(0,[z1,z2,z3,z171,z90,z6]),(0,[z158,z2,z3,z76,z5,z6]),(0,[z1,z260,z2,z3,z227,z5]),(0,[z1,z783,z2,z3,z4,z5]),(0,[z1,z328,z24,z2,z3,z5])],[(0,[z1,z2,z3,z492,z5,z121]),(0,[z687,z2,z81,z4,z5,z6]),(0,[z1,z2,z400,z4,z5,z216]),(0,[z1,z2,z166,z4,z55,z6]),(0,[z1,z2,z4,z203,z282,z6])],[(0,[z1,z2,z3,z4,z5,z33]),(0,[z1,z12,z2,z645,z5,z6]),(1,[z2,z3,z4,z5,z712]),(0,[z1,z103,z2,z3,z784,z6])]],
   [[(0,[z1,z2,z124,z4,z5,z33]),(0,[z1,z785,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z786]),(0,[z1,z2,z3,z4,z5,z787])],[],[(0,[z1,z2,z3,z788,z5,z6]),(0,[z1,z2,z3,z169,z5,z714])],[(0,[z1,z2,z3,z4,z789,z6]),(0,[z1,z2,z3,z4,z5,z714])],[(0,[z138,z2,z65,z4,z5,z6]),(0,[z1,z139,z58,z2,z4,z6]),(0,[z1,z2,z83,z400,z4,z6]),(0,[z1,z54,z3,z4,z754,z6]),(0,[z1,z58,z2,z4,z5,z59]),(0,[z1,z2,z4,z5,z772,z59]),(0,[z1,z2,z790,z4,z5,z6])],[(0,[z1,z2,z3,z791,z5,z6]),(0,[z1,z2,z3,z4,z5,z792]),(0,[z196,z2,z3,z76,z5,z6]),(0,[z1,z2,z28,z355,z5,z6]),(0,[z41,z2,z3,z4,z5,z21]),(0,[z2,z3,z4,z5,z793,z6])],[(0,[z1,z2,z3,z794,z5,z6]),(0,[z2,z3,z748,z4,z5,z6]),(0,[z1,z795,z3,z4,z5,z6]),(1,[z2,z3,z4,z711,z6]),(0,[z1,z2,z3,z4,z796,z5]),(0,[z1,z12,z2,z13,z5,z6])],[(0,[z1,z155,z2,z76,z5,z6]),(0,[z1,z2,z3,z245,z5,z216]),(0,[z1,z797,z2,z3,z4,z5])]],
   [[(0,[z1,z798,z2,z3,z5,z6]),(0,[z1,z799,z3,z4,z5,z6]),(0,[z687,z2,z3,z4,z5,z21]),(0,[z2,z800,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z6,z801]),(0,[z1,z2,z3,z713,z5,z6])],[(0,[z1,z802,z3,z4,z5,z6]),(0,[z77,z2,z3,z748,z5,z6]),(0,[z1,z209,z3,z4,z5,z406]),(0,[z1,z803,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z170,z174]),(0,[z1,z2,z804,z4,z5,z6]),(0,[z1,z2,z3,z4,z805,z198])],[(0,[z1,z2,z3,z806,z5,z6]),(0,[z1,z3,z807,z4,z5,z6]),(0,[z1,z2,z3,z808,z5,z6])],[(0,[z1,z2,z124,z4,z90,z6])],[(0,[z1,z2,z3,z809,z5,z6]),(0,[z1,z24,z2,z3,z5,z646]),(0,[z1,z98,z2,z3,z5,z6])],[(0,[z1,z2,z810,z4,z5,z6]),(0,[z1,z811,z3,z4,z5,z6]),(0,[z1,z2,z3,z267,z5,z216]),(0,[z1,z3,z187,z812,z5,z6])],[(0,[z16,z209,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z105]),(0,[z208,z2,z3,z4,z711,z6])]],
   [[(0,[z1,z2,z3,z4,z813,z6])],[(1,[z1,z2,z3,z4,z805])],[(0,[z1,z2,z4,z5,z814,z6]),(0,[z1,z2,z815,z4,z5,z6]),(0,[z1,z24,z2,z3,z5,z184]),(0,[z1,z2,z83,z4,z758,z6])],[(0,[z2,z3,z816,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z817]),(0,[z2,z3,z4,z5,z818,z6]),(0,[z1,z819,z2,z3,z4,z5]),(0,[z1,z123,z2,z3,z5,z6]),(0,[z1,z820,z2,z3,z5,z6])],[(0,[z1,z209,z3,z4,z5,z6]),(0,[z1,z2,z4,z724,z5,z6])],[(0,[z1,z2,z3,z821,z5,z6]),(0,[z1,z2,z3,z4,z5,z309]),(0,[z1,z822,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z823])],[(0,[z1,z2,z3,z4,z5,z135]),(0,[z1,z2,z724,z13,z5,z6])],[(0,[z1,z824,z3,z4,z5,z6]),(0,[z1,z2,z3,z245,z5,z406]),(0,[z1,z825,z3,z4,z5,z6]),(0,[z826,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z827]),(0,[z1,z419,z3,z4,z91,z6]),(0,[z1,z2,z828,z4,z5,z6])],[(0,[z1,z2,z3,z829,z5,z6]),(0,[z1,z3,z4,z830,z5,z6]),(0,[z1,z2,z28,z4,z5,z117]),(0,[z1,z831,z3,z4,z5,z6])],[(0,[z1,z365,z3,z207,z5,z6]),(0,[z1,z2,z3,z4,z5,z832]),(0,[z1,z2,z3,z833,z5,z6]),(0,[z1,z2,z3,z834,z5,z6]),(0,[z1,z2,z3,z4,z5,z835]),(0,[z1,z146,z3,z4,z5,z768])],[(0,[z1,z139,z2,z4,z193,z6]),(0,[z1,z2,z3,z836,z5,z6]),(0,[z1,z209,z83,z3,z4,z6]),(0,[z1,z2,z3,z5,z6,z837]),(0,[z1,z2,z3,z4,z5,z838]),(0,[z1,z2,z25,z4,z5,z193]),(0,[z1,z2,z3,z104,z120,z6])],[(0,[z1,z2,z3,z4,z839,z6]),(0,[z1,z2,z3,z4,z5,z840]),(0,[z1,z2,z841,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z842]),(0,[z2,z3,z4,z5,z843,z6])],[(0,[z1,z2,z844,z4,z5,z6]),(0,[z1,z24,z2,z3,z5,z679]),(0,[z1,z192,z807,z4,z5,z6]),(0,[z845,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z355,z5,z6]),(0,[z1,z2,z3,z267,z5,z406]),(0,[z1,z2,z3,z846,z5,z6]),(0,[z1,z2,z847,z4,z5,z6])],[(0,[z1,z98,z197,z2,z3,z198])]],
   [[(0,[z1,z2,z124,z171,z5,z6]),(0,[z1,z2,z3,z4,z90,z33]),(0,[z42,z749,z3,z4,z5,z6])],[(0,[z1,z2,z3,z848,z5,z6]),(0,[z1,z2,z3,z4,z5,z849])],[(0,[z42,z137,z49,z4,z5,z6]),(0,[z1,z109,z3,z187,z5,z6]),(0,[z196,z2,z3,z4,z5,z21]),(0,[z1,z298,z64,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z850])],[(0,[z1,z54,z3,z4,z290,z6]),(0,[z1,z851,z3,z4,z5,z6]),(0,[z77,z2,z172,z76,z5,z6]),(0,[z1,z807,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z852]),(0,[z1,z2,z3,z4,z853,z6]),(0,[z1,z2,z3,z262,z5,z221])],[(0,[z1,z2,z3,z492,z5,z186]),(0,[z1,z2,z3,z854,z5,z6]),(0,[z1,z98,z197,z2,z3,z5])],[(0,[z1,z192,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z856,z3,z4,z5,z6]),(0,[z1,z24,z2,z3,z697,z5])],[(0,[z1,z2,z3,z857,z5,z6]),(1,[z1,z3,z812,z5,z6]),(0,[z1,z197,z2,z3,z4,z198])]],
   [[(0,[z1,z2,z3,z267,z5,z6]),(0,[z1,z209,z3,z4,z17,z6]),(0,[z1,z2,z3,z5,z6,z858]),(0,[z1,z2,z3,z4,z5,z859]),(0,[z1,z2,z83,z4,z291,z6])],[(0,[z1,z2,z3,z4,z860,z6]),(0,[z27,z2,z3,z355,z5,z21]),(0,[z1,z103,z75,z2,z3,z179])],[(0,[z1,z2,z65,z86,z5,z6]),(0,[z1,z139,z2,z400,z4,z6]),(0,[z1,z2,z166,z4,z5,z6]),(0,[z1,z2,z25,z3,z262,z5]),(0,[z1,z58,z123,z2,z3,z5])],[(0,[z1,z2,z3,z4,z5,z861]),(0,[z1,z3,z4,z754,z91,z6]),(0,[z1,z24,z2,z3,z5,z261])],[(0,[z1,z2,z3,z4,z5,z862]),(0,[z1,z2,z3,z863,z5,z6]),(0,[z140,z73,z2,z3,z4,z6]),(0,[z1,z2,z166,z4,z91,z6])],[(0,[z1,z2,z3,z864,z5,z6]),(0,[z1,z865,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z866]),(0,[z1,z2,z867,z4,z5,z6]),(0,[z1,z2,z3,z4,z167,z5]),(0,[z1,z2,z4,z5,z6,z772])],[(0,[z1,z2,z3,z4,z5,z214]),(0,[z1,z2,z3,z4,z5,z121]),(0,[z138,z2,z9,z65,z4,z6])],[(0,[z1,z2,z124,z4,z5,z214]),(0,[z1,z52,z2,z3,z179,z6]),(0,[z1,z2,z83,z513,z4,z6]),(0,[z1,z2,z3,z5,z6,z868]),(0,[z1,z2,z3,z4,z869,z6]),(0,[z1,z2,z4,z5,z79,z563])]],
   [[(0,[z1,z2,z49,z434,z5,z6]),(0,[z1,z2,z511,z61,z5,z6]),(0,[z1,z94,z2,z3,z246,z5]),(0,[z1,z2,z3,z4,z784,z6])],[(0,[z1,z2,z870,z4,z5,z6]),(0,[z1,z2,z871,z4,z5,z6])],[(0,[z1,z2,z49,z4,z90,z6]),(0,[z1,z2,z3,z169,z5,z570]),(0,[z872,z2,z3,z4,z5,z6]),(0,[z1,z73,z2,z4,z481,z6]),(0,[z1,z873,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z874])],[(0,[z1,z875,z2,z4,z5,z6]),(0,[z1,z2,z3,z876,z5,z6])],[(0,[z1,z2,z3,z4,z877,z6]),(0,[z1,z2,z3,z171,z5,z33]),(0,[z1,z2,z3,z4,z878,z5]),(0,[z2,z3,z4,z5,z712,z117]),(0,[z1,z879,z3,z4,z5,z6])],[(0,[z1,z2,z880,z4,z5,z6]),(0,[z1,z881,z3,z4,z5,z6]),(1,[z1,z807,z4,z5,z6]),(0,[z1,z12,z2,z3,z5,z309]),(0,[z1,z123,z2,z25,z3,z5]),(0,[z1,z237,z197,z2,z4,z198])],[(0,[z1,z2,z3,z5,z6,z882]),(0,[z1,z2,z3,z883,z5,z6])],[(0,[z1,z2,z884,z3,z4,z6]),(0,[z1,z2,z384,z37,z5,z6]),(0,[z1,z2,z3,z885,z5,z6]),(0,[z1,z2,z3,z886,z5,z6]),(0,[z1,z2,z36,z5,z6,z550])]],
   [[(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z2,z3,z4,z5,z888]),(0,[z1,z2,z28,z4,z5,z21]),(0,[z1,z73,z260,z2,z4,z5]),(0,[z1,z197,z2,z3,z10,z198])],[(0,[z1,z889,z2,z3,z5,z6])],[(0,[z1,z2,z3,z890,z5,z6]),(0,[z1,z3,z812,z207,z5,z6]),(0,[z1,z3,z4,z812,z5,z6]),(0,[z1,z2,z3,z891,z5,z6])],[(0,[z2,z3,z748,z133,z5,z6]),(0,[z208,z560,z3,z4,z204,z6]),(0,[z1,z2,z3,z257,z5,z6]),(0,[z1,z2,z25,z4,z229,z5])],[(0,[z1,z209,z3,z4,z204,z6])],[(0,[z1,z2,z387,z4,z5,z216]),(0,[z27,z2,z3,z4,z5,z712]),(0,[z1,z2,z4,z5,z6,z264])],[(0,[z1,z3,z4,z892,z5,z6])],[(0,[z462,z2,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z893]),(0,[z684,z2,z3,z133,z5,z6]),(0,[z1,z2,z894,z4,z5,z6]),(0,[z1,z73,z2,z4,z674,z6]),(0,[z1,z2,z3,z5,z6,z714])]],
   [[(0,[z1,z2,z3,z895,z5,z6]),(0,[z1,z2,z81,z86,z5,z6])],[(0,[z1,z2,z3,z896,z5,z6]),(0,[z140,z2,z3,z4,z17,z6]),(0,[z1,z58,z2,z383,z4,z5])],[(0,[z1,z2,z28,z61,z5,z6]),(0,[z1,z54,z166,z4,z55,z6]),(0,[z1,z2,z3,z897,z5,z6])],[(0,[z2,z749,z3,z4,z5,z6]),(0,[z1,z2,z3,z898,z5,z6]),(0,[z1,z899,z2,z4,z5,z6])],[(0,[z1,z260,z2,z65,z4,z5]),(0,[z1,z2,z3,z133,z5,z105]),(0,[z1,z2,z3,z900,z5,z6]),(0,[z1,z58,z2,z3,z262,z5])],[(0,[z80,z2,z81,z86,z5,z6]),(0,[z501,z2,z3,z4,z5,z117])],[(0,[z1,z2,z172,z4,z5,z7]),(0,[z1,z2,z3,z4,z5,z901]),(0,[z1,z2,z4,z758,z74,z6]),(0,[z1,z2,z25,z4,z5,z772])],[(0,[z902,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z903,z6]),(0,[z1,z2,z4,z5,z758,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z904]),(0,[z1,z2,z3,z4,z5,z905]),(0,[z1,z58,z2,z4,z5,z265]),(0,[z1,z94,z2,z81,z5,z6])],[(0,[z1,z321,z64,z4,z361,z6]),(0,[z1,z906,z2,z3,z5,z6]),(0,[z1,z24,z2,z3,z350,z5])],[(0,[z1,z2,z3,z4,z907,z6]),(0,[z1,z75,z2,z3,z133,z5])],[(0,[z1,z2,z3,z908,z5,z6]),(0,[z1,z73,z2,z4,z74,z6]),(0,[z1,z155,z103,z2,z179,z6])],[(0,[z80,z2,z81,z4,z5,z6]),(0,[z1,z106,z3,z812,z5,z6]),(0,[z909,z2,z3,z4,z5,z6]),(0,[z1,z58,z123,z2,z5,z59]),(0,[z1,z2,z910,z4,z5,z6])],[(0,[z1,z2,z3,z434,z5,z214]),(0,[z1,z2,z387,z4,z5,z406]),(0,[z911,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z912,z6])],[(0,[z140,z2,z3,z4,z90,z6]),(0,[z664,z2,z3,z133,z5,z6]),(0,[z1,z2,z36,z3,z5,z309]),(0,[z1,z3,z4,z55,z754,z6]),(0,[z1,z2,z3,z4,z5,z913])],[(0,[z1,z2,z3,z4,z90,z214]),(0,[z1,z2,z3,z4,z5,z914]),(0,[z1,z2,z3,z4,z5,z805])]],
   [[(0,[z1,z2,z3,z4,z5,z915]),(0,[z1,z58,z2,z516,z4,z5])],[(0,[z1,z2,z3,z4,z916,z6]),(0,[z1,z2,z400,z4,z5,z406]),(0,[z1,z3,z4,z5,z6,z917]),(0,[z484,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z169,z5,z326])],[(0,[z918,z2,z3,z4,z5,z6]),(0,[z1,z919,z3,z4,z5,z6])],[(0,[z42,z137,z3,z4,z43,z6]),(0,[z57,z2,z3,z4,z5,z712]),(0,[z1,z2,z3,z920,z5,z6]),(0,[z1,z921,z2,z3,z4,z5])],[(0,[z1,z2,z49,z4,z5,z6]),(0,[z1,z2,z200,z4,z5,z6]),(0,[z1,z922,z3,z4,z5,z6]),(0,[z1,z2,z923,z4,z5,z6]),(0,[z1,z73,z209,z3,z4,z6]),(0,[z1,z73,z2,z4,z557,z6]),(0,[z1,z98,z2,z3,z99,z5])],[(0,[z1,z2,z3,z4,z5,z186]),(0,[z1,z98,z2,z3,z5,z117]),(0,[z1,z2,z3,z4,z924,z6]),(0,[z1,z2,z925,z4,z5,z6])],[(0,[z1,z2,z926,z4,z5,z6]),(0,[z132,z2,z3,z133,z5,z6]),(0,[z1,z2,z422,z4,z5,z6]),(0,[z1,z2,z3,z927,z5,z6]),(0,[z1,z533,z3,z4,z91,z6]),(0,[z1,z103,z2,z3,z79,z179])],[(0,[z1,z2,z387,z4,z5,z6]),(0,[z1,z139,z2,z95,z4,z6]),(0,[z1,z2,z928,z4,z5,z6]),(0,[z1,z929,z2,z4,z5,z6]),(0,[z1,z2,z735,z4,z5,z6]),(0,[z1,z103,z2,z3,z397,z6])]],
   [[(0,[z1,z2,z4,z5,z6,z930]),(0,[z1,z24,z2,z3,z5,z258])],[(0,[z1,z2,z3,z76,z5,z105]),(0,[z1,z192,z94,z95,z5,z6]),(0,[z931,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z932,z6]),(0,[z1,z2,z3,z4,z5,z933]),(0,[z1,z3,z4,z5,z768,z22]),(1,[z1,z2,z3,z5,z714])],[(0,[z1,z2,z934,z4,z5,z6])],[(0,[z1,z2,z400,z4,z5,z6]),(0,[z1,z151,z3,z187,z5,z309])],[(0,[z1,z94,z2,z3,z5,z6]),(0,[z1,z151,z3,z187,z5,z135]),(0,[z1,z12,z163,z2,z13,z5])],[(0,[z1,z2,z935,z4,z5,z6]),(0,[z1,z936,z2,z4,z5,z6]),(0,[z147,z2,z3,z4,z5,z117]),(0,[z1,z2,z125,z4,z203,z6]),(0,[z1,z2,z3,z4,z5,z937])],[(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z2,z3,z4,z939,z6]),(0,[z1,z2,z172,z4,z5,z105]),(0,[z1,z2,z3,z4,z99,z556])],[(0,[z1,z2,z3,z4,z5,z940]),(0,[z1,z941,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z942,z5,z6])],[(0,[z1,z2,z3,z434,z43,z6]),(0,[z1,z2,z200,z4,z5,z7]),(0,[z1,z560,z3,z245,z5,z6]),(0,[z1,z192,z227,z95,z5,z6]),(0,[z1,z2,z3,z227,z5,z6]),(0,[z1,z2,z943,z4,z5,z6]),(0,[z1,z12,z2,z724,z5,z6]),(0,[z1,z2,z3,z120,z6,z464])],[(0,[z1,z2,z944,z4,z5,z6])],[(0,[z1,z2,z3,z4,z945,z6]),(0,[z1,z2,z3,z171,z5,z214])],[(0,[z1,z2,z3,z245,z5,z6]),(0,[z1,z2,z3,z4,z361,z6]),(0,[z1,z2,z3,z946,z5,z6]),(0,[z1,z237,z2,z4,z5,z6])],[(0,[z1,z2,z947,z4,z5,z6]),(0,[z1,z948,z2,z3,z5,z6]),(0,[z1,z2,z949,z4,z5,z6]),(0,[z1,z2,z4,z5,z193,z596])],[(0,[z1,z2,z3,z4,z5,z950])],[(0,[z1,z2,z3,z951,z5,z6]),(0,[z1,z2,z3,z4,z5,z952]),(0,[z1,z192,z246,z95,z4,z5]),(0,[z1,z2,z953,z4,z5,z6]),(0,[z1,z58,z2,z4,z5,z154])]],
   [[(0,[z1,z2,z83,z4,z665,z6]),(0,[z208,z209,z3,z4,z204,z6]),(0,[z1,z560,z3,z267,z5,z6]),(0,[z1,z2,z3,z954,z5,z6]),(0,[z1,z151,z3,z812,z5,z6]),(0,[z1,z2,z3,z104,z784,z6])],[(0,[z1,z2,z49,z4,z5,z33]),(0,[z1,z2,z3,z748,z5,z6]),(0,[z1,z2,z3,z5,z955,z6])],[(0,[z1,z2,z3,z86,z5,z121]),(0,[z1,z956,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z957]),(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z2,z3,z246,z4,z5])],[(0,[z1,z2,z959,z4,z5,z6]),(0,[z1,z2,z3,z4,z960,z6])],[(0,[z1,z961,z3,z4,z5,z6])],[(0,[z1,z962,z2,z3,z4,z5]),(0,[z1,z54,z422,z4,z55,z6])],[(0,[z1,z2,z3,z4,z5,z963]),(0,[z1,z2,z3,z964,z5,z6])]],
   [[(0,[z140,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z965]),(0,[z1,z2,z3,z4,z5,z966]),(0,[z1,z2,z967,z4,z5,z6]),(0,[z1,z2,z3,z5,z784,z6]),(0,[z1,z197,z2,z3,z4,z397])],[(0,[z1,z139,z2,z64,z4,z6]),(0,[z1,z2,z3,z968,z5,z6]),(0,[z1,z969,z3,z4,z5,z6]),(0,[z1,z2,z3,z970,z5,z6]),(0,[z1,z2,z3,z4,z5,z772])],[(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z972,z2,z3,z4,z6]),(0,[z1,z2,z95,z4,z177,z6]),(0,[z1,z237,z2,z5,z6,z10])],[(0,[z1,z16,z3,z4,z90,z6]),(0,[z42,z209,z3,z4,z5,z6]),(0,[z1,z2,z3,z973,z5,z6]),(0,[z1,z321,z64,z4,z177,z6]),(0,[z1,z12,z2,z311,z5,z6])],[(0,[z1,z2,z3,z4,z6,z974]),(0,[z1,z2,z3,z4,z975,z6]),(0,[z1,z98,z2,z3,z5,z21]),(0,[z140,z119,z3,z4,z91,z6]),(0,[z1,z2,z3,z4,z5,z779]),(0,[z1,z2,z976,z4,z5,z6]),(1,[z1,z2,z4,z5,z772]),(0,[z1,z977,z2,z4,z5,z6])],[(0,[z208,z2,z3,z245,z204,z6]),(0,[z1,z978,z3,z4,z5,z6]),(0,[z1,z2,z979,z4,z5,z6])],[(0,[z1,z2,z3,z104,z92,z6]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z2,z3,z568,z5,z170]),(0,[z1,z2,z3,z4,z5,z981]),(0,[z1,z12,z2,z516,z5,z6]),(0,[z1,z2,z3,z982,z5,z6])],[(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z2,z3,z492,z5,z6]),(0,[z1,z984,z3,z4,z5,z6]),(0,[z342,z2,z189,z3,z4,z6]),(0,[z140,z2,z83,z3,z4,z6]),(0,[z1,z2,z3,z985,z5,z6])]],
   [[(0,[z1,z2,z3,z986,z5,z6])],[(0,[z1,z139,z2,z4,z74,z6]),(0,[z1,z2,z987,z4,z5,z6]),(0,[z1,z988,z2,z3,z4,z5]),(0,[z1,z989,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z990]),(0,[z1,z137,z3,z4,z90,z6]),(0,[z1,z155,z2,z4,z5,z6]),(0,[z1,z2,z36,z724,z5,z6]),(0,[z1,z2,z3,z5,z991,z6])],[(0,[z1,z2,z4,z5,z6,z992]),(0,[z1,z197,z2,z4,z264,z198])],[(0,[z1,z2,z511,z4,z5,z6]),(0,[z208,z2,z3,z267,z204,z6]),(0,[z1,z2,z993,z4,z5,z6])],[(0,[z0,z749,z3,z4,z5,z6]),(0,[z1,z151,z3,z286,z5,z6]),(0,[z994,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z995]),(0,[z1,z2,z4,z203,z6,z584])],[(0,[z1,z2,z3,z4,z996,z6]),(0,[z138,z139,z2,z65,z4,z6])],[(0,[z1,z2,z3,z997,z5,z6]),(0,[z1,z119,z3,z4,z754,z6])]],
   [[(0,[z389,z2,z3,z4,z5,z117]),(0,[z1,z2,z4,z998,z5,z6])],[(0,[z1,z12,z2,z101,z5,z6])],[(0,[z1,z999,z2,z4,z5,z6]),(0,[z77,z2,z200,z76,z5,z6]),(0,[z1,z2,z1000,z4,z5,z6])],[(0,[z1,z530,z3,z4,z91,z6]),(0,[z1,z1001,z2,z4,z5,z6]),(0,[z1002,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1003,z5,z6]),(0,[z1,z2,z9,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1004]),(0,[z1,z24,z2,z3,z5,z475])],[(0,[z1,z2,z3,z4,z43,z6]),(0,[z643,z2,z3,z4,z5,z21]),(0,[z1005,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z167,z13,z5])],[(0,[z1,z2,z3,z1006,z5,z6]),(0,[z1,z2,z124,z4,z43,z6]),(0,[z2,z81,z816,z4,z5,z6])],[(0,[z27,z2,z511,z4,z5,z21]),(0,[z1007,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1008])]],
   [[(0,[z1,z2,z1009,z3,z4,z6]),(0,[z1,z2,z3,z784,z179,z6]),(0,[z1,z2,z3,z169,z5,z362])],[(0,[z1,z2,z49,z171,z5,z6]),(0,[z1,z2,z200,z133,z5,z6]),(0,[z1,z2,z1010,z4,z5,z6])],[(0,[z1,z560,z3,z4,z5,z216]),(0,[z1,z146,z3,z4,z5,z22]),(0,[z1,z24,z2,z3,z504,z5]),(0,[z1,z2,z3,z4,z99,z100])],[(0,[z1,z2,z1011,z4,z5,z6]),(0,[z1,z2,z3,z1012,z4,z5])],[(0,[z1,z2,z3,z1013,z5,z6]),(1,[z2,z3,z748,z5,z6]),(0,[z1,z2,z1014,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1015,z6]),(0,[z1,z2,z3,z4,z5,z216]),(0,[z1,z1016,z3,z4,z5,z6]),(0,[z1,z98,z2,z5,z6,z264]),(0,[z1,z2,z3,z4,z99,z805])],[(0,[z1,z2,z3,z4,z5,z1017]),(0,[z1,z2,z28,z4,z5,z6]),(0,[z1,z2,z816,z4,z5,z6]),(0,[z1,z2,z3,z4,z177,z6]),(0,[z1,z168,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z1018,z5]),(0,[z1,z2,z3,z4,z6,z805])],[(0,[z1,z2,z3,z4,z1019,z6]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z461,z2,z65,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z3,z4,z1022,z5,z6]),(0,[z1,z2,z3,z4,z5,z1023])]],
   [[(0,[z80,z2,z81,z4,z5,z121]),(0,[z1,z2,z3,z4,z5,z1024]),(0,[z1,z2,z3,z207,z5,z309]),(0,[z1025,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1026,z4,z5]),(0,[z1,z2,z3,z4,z5,z1027]),(0,[z1,z2,z3,z86,z5,z186]),(0,[z1,z2,z3,z262,z5,z22])],[(0,[z1,z2,z3,z4,z5,z1028])],[(0,[z80,z2,z816,z4,z5,z6])],[(0,[z42,z137,z3,z434,z5,z6]),(0,[z1,z2,z3,z4,z1029,z6]),(0,[z1,z58,z2,z5,z250,z59])],[(0,[z1,z2,z3,z4,z1030,z5]),(0,[z1,z1031,z3,z4,z5,z6]),(0,[z1,z209,z3,z267,z5,z6]),(0,[z1,z181,z3,z4,z5,z221]),(0,[z1,z2,z3,z4,z5,z1032]),(0,[z1,z213,z3,z4,z5,z22])],[(0,[z42,z137,z3,z4,z90,z6]),(0,[z1,z2,z1033,z4,z5,z6]),(0,[z1,z2,z4,z1034,z5,z6]),(0,[z1,z1035,z3,z4,z5,z6])],[(0,[z1,z3,z1036,z4,z5,z6]),(0,[z1,z560,z387,z4,z5,z6]),(0,[z1,z73,z94,z2,z5,z6]),(0,[z1,z2,z3,z4,z5,z1037]),(0,[z1,z2,z1038,z4,z5,z6])]],
   [[(0,[z1,z2,z49,z4,z5,z214]),(0,[z140,z2,z3,z4,z204,z6]),(0,[z1,z2,z4,z5,z1039,z6]),(0,[z2,z3,z1040,z4,z5,z6]),(0,[z140,z2,z815,z4,z5,z6]),(0,[z1,z155,z2,z4,z5,z79]),(0,[z1041,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1042,z4,z5,z6]),(0,[z1,z2,z3,z1043,z5,z6]),(0,[z1,z2,z3,z4,z5,z1044]),(0,[z688,z2,z65,z4,z5,z6]),(0,[z1,z1045,z3,z4,z5,z6]),(0,[z1,z2,z1046,z4,z5,z6]),(0,[z27,z2,z28,z4,z5,z21])],[(0,[z1,z2,z3,z4,z43,z33]),(0,[z1,z3,z4,z5,z6,z1047]),(0,[z140,z209,z3,z4,z5,z6]),(0,[z1048,z2,z3,z4,z5,z6])],[(0,[z1,z560,z400,z4,z5,z6]),(0,[z1,z2,z1049,z4,z5,z6])],[(0,[z1,z260,z2,z81,z4,z5]),(0,[z1,z2,z1050,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1051])],[(0,[z1,z2,z3,z4,z5,z406]),(0,[z1,z1052,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1053]),(0,[z1,z24,z2,z3,z5,z381])],[(0,[z1,z2,z3,z4,z5,z1054]),(0,[z1,z354,z64,z4,z5,z6]),(0,[z1,z2,z3,z61,z5,z6]),(0,[z208,z2,z3,z4,z204,z216]),(0,[z1,z2,z1055,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1056]),(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1058,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1059,z5,z6]),(0,[z1,z2,z3,z4,z5,z1060]),(0,[z1,z2,z4,z5,z6,z1061]),(0,[z1,z3,z4,z5,z768,z6]),(0,[z1,z2,z3,z1062,z5,z6])]],
   [[(0,[z132,z2,z3,z748,z5,z6]),(0,[z1,z2,z3,z1063,z5,z6]),(0,[z1,z75,z2,z4,z5,z563])],[(0,[z1,z1064,z2,z3,z5,z6]),(0,[z1,z2,z3,z1065,z5,z6]),(0,[z1,z12,z2,z252,z5,z6]),(0,[z1,z2,z3,z4,z629,z100]),(0,[z1,z58,z2,z4,z5,z327])],[(0,[z1,z2,z25,z4,z5,z635]),(0,[z1,z103,z2,z563,z179,z6])],[(0,[z1,z2,z1066,z4,z5,z6]),(0,[z16,z3,z4,z17,z91,z6]),(0,[z2,z816,z65,z4,z5,z6]),(0,[z1,z1067,z2,z3,z4,z5]),(0,[z1,z58,z2,z4,z5,z772])],[(0,[z138,z2,z816,z4,z5,z6]),(0,[z1,z1068,z2,z3,z5,z6])],[],[(0,[z1,z2,z3,z1069,z5,z6]),(0,[z1,z2,z3,z4,z5,z1070]),(0,[z1,z1071,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1072])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z1073,z2,z3,z4,z5]),(0,[z1,z146,z107,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z1074]),(0,[z1,z2,z3,z4,z5,z1075]),(0,[z1,z24,z2,z3,z5,z408]),(0,[z1,z2,z3,z1076,z5,z6]),(0,[z1,z274,z2,z3,z4,z198]),(0,[z1,z94,z2,z203,z5,z6]),(0,[z1,z2,z3,z4,z5,z1077]),(0,[z1,z2,z3,z120,z784,z6])],[(0,[z57,z2,z3,z4,z5,z117]),(0,[z1,z2,z3,z355,z5,z117]),(0,[z27,z2,z3,z61,z5,z21]),(0,[z1,z2,z36,z553,z5,z6]),(0,[z140,z2,z3,z4,z5,z850])],[(0,[z42,z137,z3,z171,z5,z6]),(0,[z342,z2,z3,z4,z17,z6]),(0,[z89,z2,z3,z4,z5,z117]),(0,[z1,z2,z3,z1078,z4,z5]),(0,[z1,z163,z2,z3,z4,z5]),(0,[z1,z1079,z3,z4,z5,z6])],[(0,[z1,z2,z1080,z4,z5,z6]),(0,[z208,z2,z387,z4,z204,z6]),(0,[z1,z1081,z2,z3,z5,z6]),(0,[z1,z119,z3,z4,z91,z6])],[(0,[z1,z131,z95,z4,z5,z6]),(0,[z1,z3,z4,z5,z1082,z6]),(0,[z1,z2,z1083,z4,z5,z6]),(0,[z1,z2,z3,z4,z1084,z6])],[(0,[z1,z1085,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1086]),(0,[z1,z1087,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1088,z6]),(0,[z1,z2,z3,z4,z1089,z6]),(0,[z451,z2,z3,z133,z5,z6]),(0,[z2,z3,z4,z711,z204,z6]),(0,[z1,z2,z83,z4,z203,z6])],[(0,[z1,z155,z2,z133,z5,z6]),(0,[z255,z2,z3,z133,z5,z6]),(0,[z208,z2,z400,z4,z204,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1090]),(0,[z1,z2,z3,z4,z1091,z5]),(0,[z1,z260,z2,z3,z4,z5]),(0,[z1,z260,z2,z4,z203,z5]),(0,[z1,z2,z1092,z4,z5,z6])],[(1,[z2,z816,z4,z5,z6]),(0,[z1,z2,z3,z1093,z5,z6])],[(0,[z1,z2,z1094,z4,z5,z6]),(0,[z27,z2,z3,z4,z5,z21]),(0,[z1,z58,z2,z4,z5,z363]),(0,[z1,z2,z3,z1095,z5,z6])],[(0,[z1,z1096,z2,z3,z5,z6]),(0,[z1,z321,z807,z4,z5,z6]),(0,[z1,z1097,z2,z3,z4,z5])],[(0,[z1,z2,z4,z5,z6,z1098]),(0,[z1,z1099,z2,z3,z4,z5])],[(0,[z694,z16,z3,z4,z5,z6]),(0,[z1,z73,z2,z4,z156,z6]),(0,[z1,z2,z3,z5,z6,z10])],[(0,[z1,z64,z807,z4,z5,z6])],[(0,[z1,z2,z1100,z4,z5,z6]),(0,[z1,z106,z3,z207,z5,z6]),(0,[z1,z2,z3,z812,z5,z6]),(0,[z1,z2,z37,z724,z5,z6])]],
   [[(0,[z42,z137,z3,z4,z5,z6]),(0,[z1,z2,z36,z34,z5,z6])],[(0,[z42,z137,z124,z4,z5,z6]),(0,[z1,z2,z3,z1101,z5,z6]),(0,[z1,z139,z2,z83,z4,z6]),(0,[z1,z73,z2,z400,z4,z6]),(0,[z1102,z2,z3,z4,z5,z6]),(0,[z1,z2,z1103,z4,z5,z6]),(0,[z1,z103,z75,z2,z3,z5])],[(0,[z1,z2,z3,z171,z43,z6]),(0,[z1,z2,z3,z5,z6,z1104])],[],[(0,[z16,z749,z3,z4,z5,z6]),(0,[z1,z2,z200,z4,z5,z105]),(0,[z1,z298,z3,z4,z55,z6]),(0,[z1105,z2,z3,z4,z5,z6])],[(0,[z1,z58,z2,z4,z5,z541]),(0,[z1,z1106,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1107])],[(0,[z1,z2,z3,z4,z5,z1108])],[(0,[z1,z54,z3,z4,z55,z6]),(0,[z1,z155,z75,z2,z4,z5])]],
   [[(0,[z1,z24,z2,z3,z5,z619]),(0,[z1,z2,z3,z4,z754,z6]),(0,[z140,z2,z3,z891,z5,z6]),(0,[z1,z2,z3,z1109,z5,z6])],[(0,[z1,z749,z3,z4,z5,z6]),(0,[z195,z2,z3,z76,z5,z6]),(0,[z1,z2,z3,z1110,z5,z6])],[(0,[z1,z599,z3,z4,z55,z6]),(0,[z1,z337,z3,z207,z5,z6])],[(0,[z2,z3,z4,z17,z90,z6]),(0,[z1,z1111,z2,z3,z4,z6]),(0,[z1,z2,z1112,z4,z5,z6]),(0,[z1,z73,z2,z4,z205,z6]),(0,[z1,z2,z3,z4,z5,z1113]),(0,[z1,z2,z37,z5,z295,z6]),(0,[z1,z103,z2,z3,z179,z6])],[(0,[z1,z2,z3,z1114,z5,z6]),(0,[z1,z209,z387,z4,z5,z6]),(0,[z1,z75,z2,z3,z4,z5])],[(0,[z1,z2,z1115,z4,z5,z6]),(0,[z1,z2,z807,z4,z5,z6]),(0,[z1,z73,z2,z4,z210,z6]),(0,[z1,z2,z3,z4,z5,z79]),(0,[z1,z2,z4,z5,z6,z1116])],[(0,[z1,z2,z3,z434,z5,z6]),(0,[z1,z1117,z2,z3,z4,z6]),(0,[z2,z3,z4,z17,z396,z6]),(0,[z1,z24,z2,z3,z5,z638])],[(0,[z1,z2,z124,z434,z5,z6]),(0,[z1,z2,z3,z1118,z5,z6]),(0,[z241,z2,z3,z76,z5,z6]),(0,[z1,z24,z2,z3,z5,z640]),(0,[z1,z2,z3,z5,z6,z1119]),(0,[z1,z73,z2,z4,z758,z6])]],
   [[(0,[z1,z2,z3,z4,z90,z6]),(0,[z1,z2,z1120,z4,z5,z6]),(0,[z1,z2,z1121,z4,z5,z6]),(0,[z1,z209,z400,z4,z5,z6]),(0,[z1,z2,z3,z355,z5,z21]),(0,[z1,z2,z64,z4,z177,z6])],[(0,[z1,z2,z3,z4,z1122,z6]),(0,[z1,z2,z3,z4,z43,z214]),(0,[z1,z1123,z3,z4,z5,z6]),(0,[z1,z1124,z3,z4,z5,z6]),(0,[z1,z1125,z2,z4,z5,z6]),(0,[z1,z3,z4,z1126,z5,z6]),(1,[z1,z2,z3,z784,z6]),(0,[z1,z2,z3,z5,z170,z657])],[(0,[z1,z2,z1127,z4,z5,z6]),(0,[z1128,z2,z3,z4,z5,z6]),(0,[z1,z1129,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z758,z6])],[(0,[z0,z16,z3,z4,z5,z6]),(0,[z1,z237,z2,z4,z5,z21])],[(0,[z1130,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1131,z6]),(0,[z1,z197,z2,z3,z4,z805]),(0,[z1,z2,z3,z4,z100,z805])],[(0,[z42,z137,z3,z4,z5,z33]),(0,[z1,z1132,z2,z3,z5,z6]),(1,[z1,z2,z4,z758,z6])],[(0,[z1,z2,z4,z5,z1133,z6])],[(0,[z1,z2,z1134,z4,z5,z6]),(0,[z1,z321,z64,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1135])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 546) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 546).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1081)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [546, 535] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 154).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 154).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [154, 102] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_39141

theorem PEqualNP.Outside.L_meta_39141 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4205494272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4205494272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39141.solve