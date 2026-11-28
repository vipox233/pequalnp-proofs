import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41024

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4274044928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000545615c61f1c4#64 ++ 0x0000a8ac2b8c3e38#64 ++ 0x804fcfe3fc63f1c3#64 ++ 0xf009f9fc7f8c7e38#64 : BitVec 256),
   (0x8193132cc06c36d8#64 ++ 0x10326265980d86db#64 ++ 0xa3b3333cc07c7ffe#64 ++ 0xf4766667980f8fff#64 : BitVec 256),
   (0x4c2c2c370d805b68#64 ++ 0x09858586e1b00b6d#64 ++ 0xfc3c3c3f0f807fff#64 ++ 0x7f878787e1f00fff#64 : BitVec 256),
   (0x36c03fc006b681b0#64 ++ 0x26d807f800d6d036#64 ++ 0xffc03fc00fff81ff#64 ++ 0xbff807f801fff03f#64 : BitVec 256),
   (0x3b7fc0000b5b6c00#64 ++ 0x476ff800016b6d80#64 ++ 0xffffc0000ffffe07#64 ++ 0xdffff80001ffffc0#64 : BitVec 256),
   (0x1ffaba9aa0000000#64 ++ 0x83ff575354000000#64 ++ 0x5ffffffff0000007#64 ++ 0xebfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x800000000c63f1c0 0x10000000018c7e38

def z1 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x804fcfe3fc63f1c3 0xf009f9fc7f8c7e38

def z2 : W := mkw 0x0c28281200000000 0x0185050240000000 0x5c3c3c3f00000007 0x6b878787e0000000

def z3 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffc03fc00fff81ff 0xbff807f801fff03f

def z4 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffffc0000ffffe07 0xdffff80001ffffc0

def z5 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc3c3c3f0f807fff 0x7f878787e1f00fff

def z6 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b3333cc07c7ffe 0xf4766667980f8fff

def z7 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5ffffffff0000007 0xebfffffffe000000

def z8 : W := mkw 0xb7d77feddefff7fc 0x36faeffdbbdffeff 0xffffffffffffffff 0xffffffffffffffff

def z9 : W := mkw 0xcdbe3e3f8d8c5f78 0x19b7c7c7f1b18bef 0xffbc3c3f0f9c7fff 0x7ff78787e1f38fff

def z10 : W := mkw 0x000141405061a084 0x000028280a0c3410 0x0043c3c0f0638000 0x800878781e0c7000

def z11 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fb0301c00000004 0x0bf6060380000000

def z12 : W := mkw 0x200540000b5b6c00 0x4400a800016b6d80 0xa00000000ffffe00 0x1400000001ffffc0

def z13 : W := mkw 0x1b7b800000482400 0x036f700000090480 0xffffc000007c7e07 0xdffff800000f8fc0

def z14 : W := mkw 0x3240000002120000 0x0648000000424000 0xffc000000fff8007 0x9ff8000001fff000

def z15 : W := mkw 0x3fffffc00fffedb0 0x67fffff801fffdb6 0xffffffc00fffffff 0xfffffff801ffffff

def z16 : W := mkw 0x482c003709005a48 0x09058006e1200b49 0x003c003f00007e00 0x40078007e0000fc0

def z17 : W := mkw 0x893fc02cc9497e48 0x5127f80599292fc9 0x003fc03cc0007e00 0x4007f80798000fc0

def z18 : W := mkw 0xbbffd32ccb7f7ed8 0x577ffa65996fefdb 0xfffff33ccfffffff 0xfffffe6799ffffff

def z19 : W := mkw 0x324540000b5b6c00 0x4648a800016b6d80 0xffc000000ffffe07 0x9ff8000001ffffc0

def z20 : W := mkw 0x80000124402412d8 0x100000248804825b 0x00000000000001f8 0x000000000000003f

def z21 : W := mkw 0x7e6c2c370f925b68 0x0fcd8586e1f24b6d 0xfffc3c3f0fffffff 0xffff8787e1ffffff

def z22 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0x5c3c0c3f0f807e01 0x4b878187e1f00fc0

def z23 : W := mkw 0x3f7fe8120b5b6c00 0x47effd02416b6d80 0xfffffc3f0ffffe07 0xffffff87e1ffffc0

def z24 : W := mkw 0x04002c0004800120 0x0080058000900024 0xfc003c000f8001ff 0x3f80078001f0003f

def z25 : W := mkw 0x81931308c06c2490 0x10326261180d8492 0x03830300c07c0000 0x80706060180f8000

def z26 : W := mkw 0x082c000009004800 0x0105800001200900 0xfc3c00000f807e07 0x5f87800001f00fc0

def z27 : W := mkw 0x3353c000025b2400 0x466a7800004b6480 0x03c3c000007f8000 0x80787800000ff000

def z28 : W := mkw 0x37d3ffc006ffa5b0 0x66fa7ff800dff4b6 0xffc3ffc00fff81ff 0xbff87ff801fff03f

def z29 : W := mkw 0x3a6cc0000b134800 0x474d980001626900 0x5c4cc0000f838001 0x0b89980001f07000

def z30 : W := mkw 0x8080132cc02412d8 0x101002659804825b 0x0000333cc00001f8 0x200006679800003f

def z31 : W := mkw 0x3ffffa9aab5b6c00 0xc7ffff53556b6d80 0xfffffffffffffe07 0xffffffffffffffc0

def z32 : W := mkw 0x1e68a89220000000 0x83cd151244000000 0x5c4cccc330000001 0x0b89999866000000

def z33 : W := mkw 0x9ffbbbbee06c36d8 0x93ff7777dc0d86db 0xfffffffff07c7fff 0xfffffffffe0f8fff

def z34 : W := mkw 0x8113002cc0483648 0x10226005980906c9 0xa033303cc0007ffe 0x7406660798000fff

def z35 : W := mkw 0x0080130000240090 0x0010026000048012 0xa3803300007c01fe 0xb4700660000f803f

def z36 : W := mkw 0x36402cc006928120 0x26c8059800d25024 0x5c400cc00f838001 0x0b88019801f07000

def z37 : W := mkw 0x093a801aa0000000 0x8127500354000000 0x003fc03ff0000000 0x4007f807fe000000

def z38 : W := mkw 0x2000054006b681b0 0x240000a800d6d036 0xa00000000fff81f8 0x1400000001fff03f

def z39 : W := mkw 0x482c003709005a48 0x09058006e1200b49 0xa03c303f00007ffe 0x74078607e0000fff

def z40 : W := mkw 0x2000000002960030 0x240000000052c006 0x20000000039c0038 0x0400000000738007

def z41 : W := mkw 0x0005400008416000 0x0000a80001082c00 0x804fcfe3fc63f003 0xf009f9fc7f8c7e00

def z42 : W := mkw 0x3b7fc0240b5b7e48 0x476ff804816b6fc9 0xfffff03c0fffffff 0xfffffe0781ffffff

def z43 : W := mkw 0x200440000b134800 0x4400880001626900 0x000000000f838000 0x0000000001f07000

def z44 : W := mkw 0x0080130000240090 0x0010026000048012 0x00003300000001f8 0x200006600000003f

def z45 : W := mkw 0x0000002400001248 0x0000000480000249 0xa030303c00007ffe 0x7406060780000fff

def z46 : W := mkw 0x4c2c2c130d804920 0x0985858261b00924 0x5c0c0c030f800001 0x0b81818061f00000

def z47 : W := mkw 0x000544411c41e104 0x0000a88823883c20 0x804fccc33c63f003 0xd009f998678c7e00

def z48 : W := mkw 0x3353c000025b2400 0x466a7800004b6480 0xa3f3c000007ffe06 0xd47e7800000fffc0

def z49 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc30301c0f807ffc 0x1f86060381f00fff

def z50 : W := mkw 0x200545615ef7f1f4 0x2400a8ac2bdefe3e 0xa00000000ffff1f8 0x1400000001fffe3f

def z51 : W := mkw 0x8197576ddc6df7dc 0x1032eaedbb8dbefb 0xa3fffffffc7fffff 0xf47fffffff8fffff

def z52 : W := mkw 0x000444411c01c104 0x0000888823803820 0x004fcfe3fc038003 0xe009f9fc7f807000

def z53 : W := mkw 0x3e6cecc00f93c920 0x67cd9d9801f27924 0x5c4cccc00f838001 0x0b89999801f07000

def z54 : W := mkw 0x04803fc004a481b0 0x209007f800949036 0x00003fc0000001f8 0x200007f80000003f

def z55 : W := mkw 0x093fc00009496c00 0x4127f80001292d80 0x003fc00000007e00 0x4007f80000000fc0

def z56 : W := mkw 0x7e6c2cd30f92c920 0x2fcd859a61f25924 0x5c4c0cc30f838001 0x0b89819861f07000

def z57 : W := mkw 0x7eec3ff70fb6dbf8 0x2fdd87fee1f6db7f 0xfffc3fff0fffffff 0xffff87ffe1ffffff

def z58 : W := mkw 0x493fc03709497e48 0x4927f806e1292fc9 0x003fc03f00007e00 0x4007f807e0000fc0

def z59 : W := mkw 0x7f7fec370fdb7f68 0x4feffd86e1fb6fed 0xfffffc3f0fffffff 0xffffff87e1ffffff

def z60 : W := mkw 0x7e6cec130f934920 0x4fcd9d8261f26924 0x5c4ccc030f838001 0x0b89998061f07000

def z61 : W := mkw 0x3ffbfa9aa25b2400 0xc7ff7f53544b6480 0x5ffffffff07f8007 0xebfffffffe0ff000

def z62 : W := mkw 0x3a6dc0000b5b6c00 0x474db800016b6d80 0xfc4cc0000ffffe01 0x1f89980001ffffc0

def z63 : W := mkw 0x3ffffffbff7bfdc4 0xc7ffffff7fef7fb8 0xffffffffffffffc7 0xfffffffffffffff8

def z64 : W := mkw 0x8192132cc02c16d8 0x10324265980582db 0x23b0333cc01c0ffc 0x24760667980381ff

def z65 : W := mkw 0x293fc0000b5b6c00 0x4527f800016b6d80 0xa03fc0000ffffe00 0x5407f80001ffffc0

def z66 : W := mkw 0x0080120880000000 0x0010024110000000 0x0000333cc0000000 0x2000066798000000

def z67 : W := mkw 0xbfffffeccffffff8 0x77fffffd99ffffff 0xfffffffccfffffff 0xffffffff99ffffff

def z68 : W := mkw 0x1ffabfdaa4a481b0 0xa3ff57fb54949036 0x5ffffffff00001ff 0xebfffffffe00003f

def z69 : W := mkw 0x0000000000000000 0x0000000000000000 0x004fcfe3f0000003 0xe009f9fc7e000000

def z70 : W := mkw 0x0192120880000000 0x0032424110000000 0x03b3333cc0000006 0xe076666798000000

def z71 : W := mkw 0x80010124406c36d8 0x10002024880d86db 0xa0000000007c7ff8 0x14000000000f8fff

def z72 : W := mkw 0x44002c3704801368 0x08800586e090026d 0x00003c3f000001f8 0x20000787e000003f

def z73 : W := mkw 0x8085576ddc65f3dc 0x1010aaedbb8cbe7b 0x804ffffffc63f1fb 0xf009ffffff8c7e3f

def z74 : W := mkw 0x0000002400001248 0x0000000480000249 0x0000303c000001f8 0x200006078000003f

def z75 : W := mkw 0x000141605061b0c4 0x0000282c0a0c3618 0x8043c3e0f063f1c2 0xf008787c1e0c7e38

def z76 : W := mkw 0x36c03bc002368090 0x26d807780046d012 0x5fc03fc0007f8007 0xabf807f8000ff000

def z77 : W := mkw 0xa001056446feb7f8 0x340020ac88dfd6ff 0xa00000000ffffff8 0x1400000001ffffff

def z78 : W := mkw 0x1ffffffbfc61f1c4 0x83ffffff7f8c3e38 0xdffffffffc63f1c7 0xfbffffffff8c7e38

def z79 : W := mkw 0x0000054004208180 0x000000a800841030 0x80400fc00c6381c3 0xb00801f8018c7038

def z80 : W := mkw 0x8192120c800c0618 0x10324241900180c3 0x23b0301c001c0e3c 0x04760603800381c7

def z81 : W := mkw 0x16c03a8000000000 0x02d8075000000000 0x5fc03fc000000007 0xabf807f800000000

def z82 : W := mkw 0x3ffabfdaa6b681b0 0xa7ff57fb54d6d036 0xffffffffffff81ff 0xfffffffffffff03f

def z83 : W := mkw 0x3b7fc5400fffedb0 0x676ff8a801fffdb6 0xffffc0000fffffff 0xdffff80001ffffff

def z84 : W := mkw 0x8113002cc0483648 0x10226005980906c9 0x0033003cc0007e00 0x4006600798000fc0

def z85 : W := mkw 0x33530000025a2400 0x066a6000004b4480 0xfff300000ffffe07 0xdffe600001ffffc0

def z86 : W := mkw 0x3f7fecc00fdbed20 0x67effd9801fb7da4 0xffffccc00ffffe07 0xdffff99801ffffc0

def z87 : W := mkw 0x082c002409005a48 0x0105800481200b49 0xfc3c303c0f807fff 0x7f87860781f00fff

def z88 : W := mkw 0x000105615460b1c4 0x000020ac2a8c1638 0x80030fe3f06071c2 0xf00061fc7e0c0e38

def z89 : W := mkw 0x0005402158417044 0x0000a8042b082e08 0x000fc023f0007000 0x4001f8047e000e00

def z90 : W := mkw 0x36c03a8002960030 0x26d807500052c006 0x7f803000039c003c 0x0ff0060000738007

def z91 : W := mkw 0x4c2c6c771d81db6c 0x09858d8ee3b03b6d 0xfc7cfcff3f83ffff 0x7f8f9f9fe7f07fff

def z92 : W := mkw 0x3ee83fd206b681b0 0x27dd07fa40d6d036 0xfffc3fff0fff81ff 0xffff87ffe1fff03f

def z93 : W := mkw 0x16c03b8000240090 0x02d8077000048012 0xffc03fc0007c01ff 0xbff807f8000f803f

def z94 : W := mkw 0x7b7fc0370b5b7e48 0x4f6ff806e16b6fc9 0xffffc03f0ffffe07 0xdffff807e1ffffc0

def z95 : W := mkw 0x17d23a8880000000 0x02fa475110000000 0x5ff33ffcc0000007 0xebfe67ff98000000

def z96 : W := mkw 0x7e6c2cf70f92db68 0x2fcd859ee1f25b6d 0xfc7c3cff0f83ffff 0x7f8f879fe1f07fff

def z97 : W := mkw 0x80010124406c36d8 0x10002024880d86db 0xa0030320c07c7ffa 0xf4006064180f8fff

def z98 : W := mkw 0x082c000009004800 0x0105800001200900 0x003c000000007e00 0x4007800000000fc0

def z99 : W := mkw 0x36c57fc00ef7e1b0 0x26d8aff801defc36 0xffcfffc00ffff1ff 0xfff9fff801fffe3f

def z100 : W := mkw 0x8192132cc02412d8 0x103242659804825b 0x03b3333cc00001fe 0xe07666679800003f

def z101 : W := mkw 0x3b7fc0215b5b7c44 0x476ff8042b6b6f88 0xffffc023fffffe07 0xdffff8047fffffc0

def z102 : W := mkw 0x9ffaba9ea00c0618 0x93ff5753d40180c3 0x7fb0301c001c0e3c 0x0ff60603800381c7

def z103 : W := mkw 0xcc2d2d374dec7ff8 0x1985a5a6e9bd8fff 0xfc3c3c3f0ffc7fff 0x7f878787e1ff8fff

def z104 : W := mkw 0x000141405061a084 0x000028280a0c3410 0x0000000000638000 0x00000000000c7000

def z105 : W := mkw 0x0400280000000000 0x0080050000000000 0x5c003c0000000007 0x2b80078000000000

def z106 : W := mkw 0x3ffaba9aa2960030 0xa7ff57535452c006 0x7fb0301c039c003c 0x0ff6060380738007

def z107 : W := mkw 0x2000044006928120 0x2400008800d25024 0x000000000f838000 0x0000000001f07000

def z108 : W := mkw 0x1b7a800000000000 0x036f500000000000 0x5fffc00000000007 0xcbfff80000000000

def z109 : W := mkw 0x0dbaba9aa0000000 0x81b7575354000000 0x003ffffff0000000 0x6007fffffe000000

def z110 : W := mkw 0x3ffffa9aab5b6c00 0xc7ffff53556b6d80 0xfffff01c0ffffe07 0xdffffe0381ffffc0

def z111 : W := mkw 0x0001000000482400 0x0000200000090480 0xa0000000007c7e00 0x14000000000f8fc0

def z112 : W := mkw 0x8080132cc02412d8 0x101002659804825b 0xa380333cc07c01fe 0xb4700667980f803f

def z113 : W := mkw 0x0005402158417044 0x0000a8042b082e08 0x0000000000007000 0x0000000000000e00

def z114 : W := mkw 0x4c28283601801a68 0x09850506c030034d 0xfc30303c03807ffe 0x7f86060780700fff

def z115 : W := mkw 0xbb7fc1244b7f7ed8 0x576ff824896fefdb 0xffffc0000fffffff 0xdffff80001ffffff

def z116 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xff8030000fff81fc 0x1ff0060001fff03f

def z117 : W := mkw 0x36c03a8002960030 0x26d807500052c006 0xffc030000fff803f 0x9ff8060001fff007

def z118 : W := mkw 0x8193536cd06db6dc 0x10326a6d9a0db6db 0xa3f3f3fcf07ffffe 0xf47e7e7f9e0fffff

def z119 : W := mkw 0x4c2c2c330d805960 0x0985858661b00b2c 0xdc0c0c230f8071c3 0x7b81818461f00e38

def z120 : W := mkw 0x5ffebebfad805b68 0x8bffd7d7f5b00b6d 0xffffffffff807fff 0xfffffffffff00fff

def z121 : W := mkw 0x1f7aa89aa0000000 0x83ef551354000000 0x5c7fccfff0000001 0x4b8ff99ffe000000

def z122 : W := mkw 0x000405615c20d1c4 0x000080ac2b841a38 0x800c0fe3fc0071c3 0x700181fc7f800e38

def z123 : W := mkw 0x5e6cac932d804920 0x8bcd959265b00924 0x5c4cccc33f800001 0x0b89999867f00000

def z124 : W := mkw 0x3ffaba80039e0c30 0x67ff57500073c186 0x7fb03000039c0e3c 0x0ff60600007381c7

def z125 : W := mkw 0x84803fecc4a493f8 0x309007fd9894927f 0x00003ffcc00001f8 0x200007ff9800003f

def z126 : W := mkw 0x1f7aa81200000000 0x03ef550240000000 0x5ffffc3f00000007 0xebffff87e0000000

def z127 : W := mkw 0x3eecffc00fb7c9b0 0x67dd9ff801f6f936 0xffccffc00fff81ff 0xbff99ff801fff03f

def z128 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffcfffe3ffff81ff 0xfff9fffc7ffff03f

def z129 : W := mkw 0x1640288000000000 0x02c8051000000000 0x5c400cc000000001 0x0b88019800000000

def z130 : W := mkw 0xb7d33fecc6feb7f8 0x36fa67fd98dfd6ff 0xfff33ffccfffffff 0xfffe67ff99ffffff

def z131 : W := mkw 0x89bb933ee06c36d8 0x91377267dc0d86db 0xa3bff33ff07c7ffe 0xf477fe67fe0f8fff

def z132 : W := mkw 0x3f7fe8922b5b6c00 0xc7effd12456b6d80 0xffffccc33ffffe07 0xdffff99867ffffc0

def z133 : W := mkw 0x093a801aa0000000 0x8127500354000000 0x007fcffff0000003 0xe00ff9fffe000000

def z134 : W := mkw 0x4000000401800a28 0x0800000080300145 0x2000000003800e38 0x04000000007001c7

def z135 : W := mkw 0x4828001601000a08 0x09050002c0200141 0x0030001c00000e00 0x00060003800001c0

def z136 : W := mkw 0x2000014002368090 0x240000280046d012 0x00000000007f8000 0x00000000000ff000

def z137 : W := mkw 0x4000042504801368 0x08000084a090026d 0x00000000000001f8 0x000000000000003f

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc0000000f800007 0x1f80000001f00000

def z139 : W := mkw 0x7eec3fd30fb6c9b0 0x2fdd87fa61f6d936 0xffcc3fc30fff81ff 0xbff987f861fff03f

def z140 : W := mkw 0x36c43fe10eb6d1f0 0x26d887fc21d6da3e 0xffcc3fe30ffff1ff 0xfff987fc61fffe3f

def z141 : W := mkw 0x17d2ba88a0000000 0x82fa575114000000 0x5fc3ffc0f0000007 0xabf87ff81e000000

def z142 : W := mkw 0x0192120880000000 0x0032424110000000 0x03b0301c00000004 0x0076060380000000

def z143 : W := mkw 0x000444411c01c104 0x0000888823803820 0x004cccc33c038001 0x0009999867807000

def z144 : W := mkw 0x0000002150001044 0x000000042a000208 0x00000023f0000000 0x000000047e000000

def z145 : W := mkw 0x8192122c800c1658 0x10324245900182cb 0xa3b0303c001c7ffe 0x7476060780038fff

def z146 : W := mkw 0x893b803ee0483648 0x91277007dc0906c9 0x003fc03ff0007e00 0x4007f807fe000fc0

def z147 : W := mkw 0x000544210c417140 0x0000a88421882e28 0x804fcc230c63f1c3 0xf009f984618c7e38

def z148 : W := mkw 0x32c013c002368090 0x265802780046d012 0xa3c033c0007f81fe 0xb4780678000ff03f

def z149 : W := mkw 0x3ffaba9aa2960030 0xa7ff57535452c006 0x7ffffffff39c003f 0xeffffffffe738007

def z150 : W := mkw 0xbffffbbeeb7f7ed8 0xd7ffff77dd6fefdb 0xffffffffffffffff 0xffffffffffffffff

def z151 : W := mkw 0x0c28281200000000 0x0185050240000000 0x5c0c0c0300000001 0x0b81818060000000

def z152 : W := mkw 0x3ffabedaa6928120 0xa7ff57db54d25024 0x5fffffffff838007 0xebfffffffff07000

def z153 : W := mkw 0x3ffabfc007be8db0 0x67ff57f800f7d1b6 0xfff03fc00fff8fff 0xbffe07f801fff1ff

def z154 : W := mkw 0x4c28281601800a28 0x09850502c0300145 0x7c30301c03800e3c 0x0f860603807001c7

def z155 : W := mkw 0xffff3fffcffefff8 0x3fffe7fff9ffdfff 0xffff3fffcfffffff 0xffffe7fff9ffffff

def z156 : W := mkw 0x0192120880000000 0x0032424110000000 0x03fffffff0000007 0xe07ffffffe000000

def z157 : W := mkw 0x000545655c61f3cc 0x0000a8acab8c3e79 0xa07ffffffc63ffff 0xf40fffffff8c7fff

def z158 : W := mkw 0x4c282c1605800b28 0x09850582c0b00165 0xfc303c1c0f800fff 0x3f86078381f001ff

def z159 : W := mkw 0x33d293c8a2368090 0xa67a52791446d012 0x03c3c3c0f07f8000 0x807878781e0ff000

def z160 : W := mkw 0x80811324406c36d8 0x10102264880d86db 0xa3803300007c7ffe 0xb4700660000f8fff

def z161 : W := mkw 0x6c2c2d770fb6dbf8 0x2d8585aee1f6db7f 0xfc3c3c3f0fffffff 0x7f878787e1ffffff

def z162 : W := mkw 0x8080132cc02412d8 0x101002659804825b 0xa030333cc0007ffe 0x7406066798000fff

def z163 : W := mkw 0x36c57fe15ef7f1f4 0x26d8affc2bdefe3e 0xffcfffe3fffff1ff 0xfff9fffc7ffffe3f

def z164 : W := mkw 0x4d3fec370dc97f68 0x49a7fd86e1b92fed 0xfc3ffc3f0f807fff 0x7f87ff87e1f00fff

def z165 : W := mkw 0x1ffbba9aa0482400 0x83ff775354090480 0xfffffffff07c7e07 0xfffffffffe0f8fc0

def z166 : W := mkw 0x04803a9aa0000000 0x8090075354000000 0x0000301c00000000 0x0000060380000000

def z167 : W := mkw 0x36c17fc056f7a1b4 0x26d82ff80adef436 0xffc3ffc0ffff81ff 0xbff87ff81ffff03f

def z168 : W := mkw 0x13d29288a0000000 0x827a525114000000 0x03c3c3c0f0000000 0x807878781e000000

def z169 : W := mkw 0x04056d615ce1f1e4 0x0080adac2b9c3e3c 0xfc4fffe3ffe3f1ff 0xff89fffc7ffc7e3f

def z170 : W := mkw 0xcdbf3f3fcdec7ff8 0x19b7e7e7f9bd8fff 0xffbf3f3fcffc7fff 0xfff7e7e7f9ff8fff

def z171 : W := mkw 0x3b7a8000031a0c00 0x476f500000634180 0x7fb00000039c0e04 0x0ff60000007381c0

def z172 : W := mkw 0x400404250d805b68 0x08008084a1b00b6d 0xa00000000f807ff8 0x1400000001f00fff

def z173 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000fe3f0000000 0x200001fc7e000000

def z174 : W := mkw 0x0c28283600001248 0x01850506c0000249 0xfc3c3c3f00007fff 0x7f878787e0000fff

def z175 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0x0383333cc07c01f8 0xa0706667980f803f

def z176 : W := mkw 0x4c2d6d775de1fbec 0x0985adaeebbc3f7d 0xfc3c3c3f0fe3ffff 0x7f878787e1fc7fff

def z177 : W := mkw 0x32c0128002160010 0x265802500042c002 0x03800000001c0000 0x0070000000038000

def z178 : W := mkw 0x3ffabfc006b681b0 0x27ff57f800d6d036 0xffffffc00fff81ff 0xfffffff801fff03f

def z179 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffb000000ffffe04 0x1ff6000001ffffc0

def z180 : W := mkw 0x1a68800000000000 0x034d100000000000 0x5c4cc00000000001 0x0b89980000000000

def z181 : W := mkw 0x04803a9aa0000000 0x8090075354000000 0x00003ffff0000000 0x200007fffe000000

def z182 : W := mkw 0x81931308c06c2490 0x10326261180d8492 0xa3b30300c07c7e06 0xd4766060180f8fc0

def z183 : W := mkw 0x2000054006b681b0 0x240000a800d6d036 0xa0400fc00fff81fb 0xb40801f801fff03f

def z184 : W := mkw 0x8193176dd46cb7dc 0x103262edba8d96fb 0xa3b33ffff07c7ffe 0xf47667fffe0f8fff

def z185 : W := mkw 0x93d393ace06c36d8 0x927a72759c0d86db 0xa3f3f3fcf07c7ffe 0xf47e7e7f9e0f8fff

def z186 : W := mkw 0x32c013c002368090 0x265802780046d012 0x03c003c0007f8000 0x80780078000ff000

def z187 : W := mkw 0xb3d3d32cc27f36d8 0x567a7a65984fe6db 0xa3f3f33cc07ffffe 0xf47e7e67980fffff

def z188 : W := mkw 0x011745615c69f5c4 0x0022e8ac2b8d3eb8 0xa3ffcfe3fc7fffc7 0xf47ff9fc7f8ffff8

def z189 : W := mkw 0x000404210c005140 0x0000808421800a28 0x800c0c230c0071c3 0x7001818461800e38

def z190 : W := mkw 0x4c2d6d775de1fbec 0x0985adaeebbc3f7d 0xfc7fffffffe3ffff 0xff8ffffffffc7fff

def z191 : W := mkw 0x3f7fec000fdb6d20 0x47effd8001fb6da4 0xfffffc000fffffff 0xffffff8001ffffff

def z192 : W := mkw 0xb3d313c8c27ea490 0x367a6279184fd492 0x03c303c0c07f8000 0x80786078180ff000

def z193 : W := mkw 0x04803a8000840030 0x2090075000108006 0x0000300000000038 0x0000060000000007

def z194 : W := mkw 0x0004000008004000 0x0000800001000800 0x800c00000c007003 0x5001800001800e00

def z195 : W := mkw 0x0c282c1204800120 0x0185058240900024 0xfc3c3c3f0f8001ff 0x7f878787e1f0003f

def z196 : W := mkw 0x482c04250d805b68 0x09058084a1b00b6d 0xfc3c00000f807fff 0x5f87800001f00fff

def z197 : W := mkw 0x3b7fc5615f7bfdc4 0x476ff8ac2bef7fb8 0xffffc0000fffffc7 0xdffff80001fffff8

def z198 : W := mkw 0x7eec3eb70f965b78 0x2fdd87d6e1f2cb6f 0xffbc3c3f0f9c7fff 0x7ff78787e1f38fff

def z199 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x80000fe3fc63f1c0 0x300001fc7f8c7e38

def z200 : W := mkw 0x400545655de1fbec 0x0800a8acabbc3f7d 0xa04fcfe3ffe3fffb 0xf409f9fc7ffc7fff

def z201 : W := mkw 0x04803fe154a491f4 0x209007fc2a94923e 0x00003fe3f00001f8 0x200007fc7e00003f

def z202 : W := mkw 0x482d403759417a4c 0x0905a806eb282f49 0x003fc03ff0007e00 0x4007f807fe000fc0

def z203 : W := mkw 0x3357c5615e7bf5c4 0x466af8ac2bcf7eb8 0x83cfcfe3fc7ff1c3 0xf079f9fc7f8ffe38

def z204 : W := mkw 0x0113000000482400 0x0022600000090480 0xa3b30000007c7e06 0xd4766000000f8fc0

def z205 : W := mkw 0x32c0130002360090 0x065802600046c012 0xffc033000fff81ff 0xbff8066001fff03f

def z206 : W := mkw 0x0005400009496c00 0x4000a80001292d80 0x0000000000007e00 0x0000000000000fc0

def z207 : W := mkw 0x8197576ddc6df7dc 0x1032eaedbb8dbefb 0xa3b3333ccc7ffffe 0xf4766667998fffff

def z208 : W := mkw 0x00010120406030c0 0x00002024080c0618 0x804fcfe3f06071c3 0xf009f9fc7e0c0e38

def z209 : W := mkw 0x3a6c00000b124800 0x074d800001624900 0xfffc00000ffffe07 0xdfff800001ffffc0

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0x004cccc330000001 0x0009999866000000

def z211 : W := mkw 0x0000014000208080 0x0000002800041010 0x004003c000638000 0x80080078000c7000

def z212 : W := mkw 0x16c03fc004208180 0x02d807f800841030 0xdfc03fc00c6381c7 0xbbf807f8018c7038

def z213 : W := mkw 0x13d29288a0000000 0x827a525114000000 0x0380000000000000 0x0070000000000000

def z214 : W := mkw 0x3fffffe15ffffdf4 0x67fffffc2bffffbe 0xffffffe3ffffffff 0xfffffffc7fffffff

def z215 : W := mkw 0xb7d33bacc2fe36f8 0x36fa6775985fc6df 0xffb3333cc3fc7ffe 0xfff66667987f8fff

def z216 : W := mkw 0x8dbb3b3ec06c36d8 0x11b76767d80d86db 0xffbf3f3fc07c7fff 0xfff7e7e7f80f8fff

def z217 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc0c0c030f807ff9 0x1f81818061f00fff

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c0c2300000003 0x6001818460000000

def z219 : W := mkw 0x00000561542091c4 0x000000ac2a841238 0x00000fe3f00001c0 0x200001fc7e000038

def z220 : W := mkw 0x1e68a89220000000 0x83cd151244000000 0x5c7cfcff30000007 0x6b8f9f9fe6000000

def z221 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc7fffffff807fff 0xff8ffffffff00fff

def z222 : W := mkw 0x33d3d288a25b2400 0xc67a7a51144b6480 0x03c3c3c0f07f8000 0x807878781e0ff000

def z223 : W := mkw 0x80010124406c36d8 0x10002024880d86db 0xa030303c007c7ffe 0x74060607800f8fff

def z224 : W := mkw 0x0000040004000100 0x0000008000800020 0x80000c000c0001c3 0x3000018001800038

def z225 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030303c00000006 0x6006060780000000

def z226 : W := mkw 0x3b7e80000b1a4c00 0x476fd00001634980 0xffbc00000f9c7e07 0x5ff7800001f38fc0

def z227 : W := mkw 0x093a800000000000 0x0127500000000000 0x003fc00000000000 0x4007f80000000000

def z228 : W := mkw 0x24002d4006b681b0 0x248005a800d6d036 0xfc003c000fff81ff 0x3f80078001fff03f

def z229 : W := mkw 0x482d45775d61fbcc 0x0905a8aeebac3f79 0x807fcffffc63ffc3 0xf00ff9ffff8c7ff8

def z230 : W := mkw 0x008557615c65f1d4 0x0010aaec2b8cbe3a 0xa3cfffe3fc7ff1ff 0xf479fffc7f8ffe3f

def z231 : W := mkw 0x800545655c6df7dc 0x1000a8acab8dbefb 0xa00000000c7ffff8 0x14000000018fffff

def z232 : W := mkw 0x00054121586170c4 0x0000a8242b0c2e18 0x800fc323f06071c2 0xf001f8647e0c0e38

def z233 : W := mkw 0x5ffffffffde1fbec 0x8bffffffffbc3f7d 0xffffffffffe3ffff 0xfffffffffffc7fff

def z234 : W := mkw 0x0192130880240090 0x0032426110048012 0xa3b3333cc07c01fe 0xf4766667980f803f

def z235 : W := mkw 0x4d3eac3fad805b68 0x89a7d587f5b00b6d 0xfc3ffc3fff807fff 0x7f87ff87fff00fff

def z236 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x804cccc33c63f1c1 0x10099998678c7e38

def z237 : W := mkw 0x1ee83a9200000000 0x03dd075240000000 0x5ffc3fff00000007 0xebff87ffe0000000

def z238 : W := mkw 0x1ffffa9aa9496c00 0xc3ffff5355292d80 0x5ffffffff0007e07 0xebfffffffe000fc0

def z239 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffffcfe3fffffe07 0xfffff9fc7fffffc0

def z240 : W := mkw 0x093fc02159497c44 0x4127f8042b292f88 0x003fc023f0007e00 0x4007f8047e000fc0

def z241 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x800c0c230c63f1c3 0x70018184618c7e38

def z242 : W := mkw 0x8193120c804c2618 0x10326241900984c3 0xa3b3301c007c7e3e 0xd4766603800f8fc7

def z243 : W := mkw 0x3ffffa800bdf6c30 0x67ffff50017bed86 0xfffff0000ffffe3f 0xdffffe0001ffffc7

def z244 : W := mkw 0x3b7fc01aab5b6c00 0xc76ff803556b6d80 0xffffc03ffffffe07 0xdffff807ffffffc0

def z245 : W := mkw 0x0828000000000000 0x0105000000000000 0x5c3c000000000007 0x4b87800000000000

def z246 : W := mkw 0x7eed7ff75ff7fbfc 0x2fddaffeebfeff7f 0xffffffffffffffff 0xffffffffffffffff

def z247 : W := mkw 0x0005400008416000 0x0000a80001082c00 0x804fc0000c63f003 0xd009f800018c7e00

def z248 : W := mkw 0x8081132cc06432d8 0x10102265980c865b 0x8003333cc06071fa 0xf0006667980c0e3f

def z249 : W := mkw 0x800545655c6df7dc 0x1000a8acab8dbefb 0xa04fcfe3fc7ffffb 0xf409f9fc7f8fffff

def z250 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0x003c3c3f00007ff8 0x60078787e0000fff

def z251 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0x5c7fc0000f83fe01 0x4b8ff80001f07fc0

def z252 : W := mkw 0xb6c13fe446feb7f8 0x36d827fc88dfd6ff 0xffc03fc00fffffff 0xbff807f801ffffff

def z253 : W := mkw 0x3ffaba9aa2120000 0x87ff575354424000 0xffffffffffff8007 0xfffffffffffff000

def z254 : W := mkw 0x093fc03bf8417044 0x8127f8077f082e08 0x003fc03ff0007000 0x4007f807fe000e00

def z255 : W := mkw 0x36c03e8006960130 0x26d807d000d2c026 0xff803c000f9c01ff 0x3ff0078001f3803f

def z256 : W := mkw 0x0400281200000000 0x0080050240000000 0x00003c3f00000000 0x20000787e0000000

def z257 : W := mkw 0x0c2d6d735c61f1c4 0x0185adae6b8c3e38 0xdc7ffffffc63f1c7 0xfb8fffffff8c7e38

def z258 : W := mkw 0x36c03fe406b693f8 0x26d807fc80d6d27f 0xfff03ffc0fffffff 0xfffe07ff81ffffff

def z259 : W := mkw 0xcdba3a1e818c0e38 0x19b74743d03181c7 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z260 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b0301c007c7ffc 0x14760603800f8fff

def z261 : W := mkw 0x00010124406032c8 0x00002024880c0659 0xa033333cc0607ffe 0xf4066667980c0fff

def z262 : W := mkw 0x97d33bacc06c36d8 0x12fa6775980d86db 0xfff33ffcc07c7fff 0xfffe67ff980f8fff

def z263 : W := mkw 0x0112000880000000 0x0022400110000000 0x0033003cc0000000 0x4006600798000000

def z264 : W := mkw 0x8112000c80080608 0x10224001900100c1 0x0030001c00000e00 0x00060003800001c0

def z265 : W := mkw 0x0000000400000208 0x0000000080000041 0x2030301c00000e3c 0x04060603800001c7

def z266 : W := mkw 0x89bf132cc96c7ed8 0x1137e265992d8fdb 0xffbf333ccffc7fff 0xfff7e66799ff8fff

def z267 : W := mkw 0x082c000009004800 0x0105800001200900 0x5c0c00000f800001 0x0b81800001f00000

def z268 : W := mkw 0x3240054006b681b0 0x264800a800d6d036 0xffc000000fff81ff 0x9ff8000001fff03f

def z269 : W := mkw 0xa00541244b7f7ed8 0x5400a824896fefdb 0xa00000000ffffff8 0x1400000001ffffff

def z270 : W := mkw 0x200540000b5b6c00 0x4400a800016b6d80 0xa04fc0000ffffe03 0xd409f80001ffffc0

def z271 : W := mkw 0x0113002400483648 0x00226004800906c9 0xa3b3303c007c7ffe 0xf4766607800f8fff

def z272 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3fffffff07c7fff 0xf47ffffffe0f8fff

def z273 : W := mkw 0x200545615ef7f1f4 0x2400a8ac2bdefe3e 0xa04fcfe3fffff1fb 0xf409f9fc7ffffe3f

def z274 : W := mkw 0x0001002040403040 0x0000200408080608 0x00030020c0007000 0x4000600418000e00

def z275 : W := mkw 0x0004000009004800 0x0000800001200900 0xa00000000f807e00 0x1400000001f00fc0

def z276 : W := mkw 0x36402c0006920120 0x06c8058000d24024 0xffc03c000fff81ff 0xbff8078001fff03f

def z277 : W := mkw 0x04803f0004a401b0 0x009007e000948036 0xff803f000ffc01ff 0xbff007e001ff803f

def z278 : W := mkw 0x3b7a8000031a0c00 0x476f500000634180 0xfff000000fff8e07 0x9ffe000001fff1c0

def z279 : W := mkw 0x04002c2404801368 0x008005848090026d 0xfc303c3c0f807fff 0x7f86078781f00fff

def z280 : W := mkw 0x0001010040602080 0x00002020080c0410 0x00030300c0600000 0x80006060180c0000

def z281 : W := mkw 0x44002c3704801368 0x08800586e090026d 0xa0303c3f00007ffe 0x74060787e0000fff

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400fc000000003 0xa00801f800000000

def z283 : W := mkw 0x0000404010018004 0x0000080802003000 0x0040c0c030038000 0x0008181806007000

def z284 : W := mkw 0x8113002cc0483648 0x10226005980906c9 0xa3b3003cc07c7e06 0xd4766007980f8fc0

def z285 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0x5fcfc0000fff8001 0x8bf9f80001fff000

def z286 : W := mkw 0xc00505254dec7ff8 0x1800a0a4a9bd8fff 0xa00000000ffc7ff8 0x1400000001ff8fff

def z287 : W := mkw 0x32c017c006368190 0x265802f800c6d032 0x83c00fc00c7f81c3 0xb07801f8018ff038

def z288 : W := mkw 0x36402dc006b681b0 0x26c805b800d6d036 0xfc400cc00fff81f9 0x1f88019801fff03f

def z289 : W := mkw 0x17d2ba9aa0000000 0x82fa575354000000 0x03c3fffff0000000 0xa0787ffffe000000

def z290 : W := mkw 0x0000044114008104 0x0000008822801020 0x00000cc330000000 0x0000019866000000

def z291 : W := mkw 0x4c2d2d374de07be8 0x0985a5a6e9bc0f7d 0xfc3f3f3fcfe07fff 0xff87e7e7f9fc0fff

def z292 : W := mkw 0x3b7fc1405b7bec84 0x476ff8280b6f7d90 0xffffc3c0fffffe07 0xdffff8781fffffc0

def z293 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x000fcfe3f00071c0 0x6001f9fc7e000e38

def z294 : W := mkw 0x3240000002120000 0x0648000000424000 0x5c4000000f838001 0x0b88000001f07000

def z295 : W := mkw 0x00811320406430d0 0x00102264080c861a 0xa3833320c07c71fe 0xf4706664180f8e3f

def z296 : W := mkw 0x3b7fc5615f7bfdc4 0x476ff8ac2bef7fb8 0xffffcfe3ffffffc7 0xfffff9fc7ffffff8

def z297 : W := mkw 0x04803a9aa0000000 0x8090075354000000 0x004ffffff0000003 0xe009fffffe000000

def z298 : W := mkw 0xb7d23fcc86be87b8 0x36fa47f990d7d0f7 0xfff03fdc0fff8fff 0xbffe07fb81fff1ff

def z299 : W := mkw 0x400545655de1fbec 0x0800a8acabbc3f7d 0xa00000000fe3fff8 0x1400000001fc7fff

def z300 : W := mkw 0x36c03b8002b600b0 0x26d807700056c016 0xff80330003fc01fe 0xbff00660007f803f

def z301 : W := mkw 0x3ffabbdaa2368090 0xa7ff577b5446d012 0x5ffffffff07f8007 0xebfffffffe0ff000

def z302 : W := mkw 0x8117402dd849764c 0x1022e805bb092ec9 0x003fc03ff0007e00 0x4007f807fe000fc0

def z303 : W := mkw 0xa197532ccb7f7ed8 0x5432ea65996fefdb 0xa3b3333ccffffffe 0xf476666799ffffff

def z304 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x80400fc00c63f1c3 0xb00801f8018c7e38

def z305 : W := mkw 0x04002c0004800120 0x0080058000900024 0x5c000c000f800001 0x0b80018001f00000

def z306 : W := mkw 0x9ffbbabee0483648 0x93ff7757dc0906c9 0x5ffffffff0007e07 0xebfffffffe000fc0

def z307 : W := mkw 0x0000001aa0000000 0x8000000354000000 0x0000003ff0000000 0x00000007fe000000

def z308 : W := mkw 0x9ffaba9ea00c0618 0x93ff5753d40180c3 0x7ffffffff01c0e3f 0xeffffffffe0381c7

def z309 : W := mkw 0x36402dc006b281a0 0x26c805b800d65034 0xdc400fc00fe381c3 0xbb8801f801fc7038

def z310 : W := mkw 0x0192120880000000 0x0032424110000000 0x03830300c0000000 0x8070606018000000

def z311 : W := mkw 0x4c2c2c130d804920 0x0985858261b00924 0x5c3c3c3f0f800007 0x6b878787e1f00000

def z312 : W := mkw 0x0000000000000000 0x0000000000000000 0xa030000000007e06 0x5406000000000fc0

def z313 : W := mkw 0xa193176cc6feb7f8 0x343262ed98dfd6ff 0xa3b3333ccffffffe 0xf476666799ffffff

def z314 : W := mkw 0xc197172dcdec7ff8 0x1832e2e5b9bd8fff 0xa3b3333ccffc7ffe 0xf476666799ff8fff

def z315 : W := mkw 0x000541405861e084 0x0000a8280b0c3c10 0x804fc3c0fc63f003 0xd009f8781f8c7e00

def z316 : W := mkw 0xc93f003fc9487e48 0x1927e007f9290fc9 0x003f003fc0007e00 0x4007e007f8000fc0

def z317 : W := mkw 0x4c2d6d735de1f9e4 0x0985adae6bbc3f3c 0xdc4fcfe3ffe3f1c3 0xfb89f9fc7ffc7e38

def z318 : W := mkw 0x093f000009486c00 0x0127e00001290d80 0xffbf00000ffc7e07 0xdff7e00001ff8fc0

def z319 : W := mkw 0x36402cc006928120 0x26c8059800d25024 0xfc403cc00f8381ff 0x3f88079801f0703f

def z320 : W := mkw 0xbbfa920c831e0e18 0x577f52419063c1c3 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z321 : W := mkw 0x44002d7754a093ec 0x088005aeea94127d 0x00003ffff00001f8 0x200007fffe00003f

def z322 : W := mkw 0x4c28281201800820 0x0985050240300104 0x5c00000003800000 0x0b80000000700000

def z323 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0x5c403fc00f8381f9 0x2b8807f801f0703f

def z324 : W := mkw 0x0000054004208180 0x000000a800841030 0x800000000c6381c0 0x10000000018c7038

def z325 : W := mkw 0x00000561542091c4 0x000000ac2a841238 0x80400fe3fc6381c3 0xb00801fc7f8c7038

def z326 : W := mkw 0x0004002108005040 0x0000800421000a08 0x000c002300007000 0x4001800460000e00

def z327 : W := mkw 0x0192122c80001248 0x0032424590000249 0xa3b3333cc0007ffe 0xf476666798000fff

def z328 : W := mkw 0x000404210c005140 0x0000808421800a28 0x800000000c0071c0 0x1000000001800e38

def z329 : W := mkw 0x324540000a536000 0x0648a800014a6c00 0xffcfc0000ffff007 0xdff9f80001fffe00

def z330 : W := mkw 0x04042c210c805160 0x0080858421900a2c 0xfc0c3c230f8071ff 0x7f81878461f00e3f

def z331 : W := mkw 0x7f7aa816039a0e28 0x4fef5502c07341c5 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z332 : W := mkw 0x44042c370c805368 0x08808586e1900a6d 0x800c3c3f0c0071fb 0x70018787e1800e3f

def z333 : W := mkw 0x0000054004208180 0x000000a800841030 0x804fcfe3fc6381c3 0xf009f9fc7f8c7038

def z334 : W := mkw 0x000141405061a084 0x000028280a0c3410 0x004fcfe3f0638003 0xe009f9fc7e0c7000

def z335 : W := mkw 0x0001000000402000 0x0000200000080400 0x8003000000607002 0xd0006000000c0e00

def z336 : W := mkw 0x5ffebabfa9005a48 0x8bffd757f5200b49 0x5ffffffff0007e07 0xebfffffffe000fc0

def z337 : W := mkw 0x3240c00002130000 0x4648180000426000 0x0040c00000038000 0x0008180000007000

def z338 : W := mkw 0x1ffffabbf8417044 0x83ffff577f082e08 0x5ffffffff0007007 0xebfffffffe000e00

def z339 : W := mkw 0x7f7eac370f9a5f68 0x4fefd586e1f34bed 0xffbc3c3f0f9c7fff 0x7ff78787e1f38fff

def z340 : W := mkw 0x4004002509005a48 0x08008004a1200b49 0x0000000000007e00 0x0000000000000fc0

def z341 : W := mkw 0x0005402158417044 0x0000a8042b082e08 0x004fcfe3f0007003 0xe009f9fc7e000e00

def z342 : W := mkw 0xb3d313ecc27eb6d8 0x367a627d984fd6db 0xa3f333fcc07ffffe 0xf47e667f980fffff

def z343 : W := mkw 0x0001400050412004 0x000028000a082400 0x0003c000f0000000 0x000078001e000000

def z344 : W := mkw 0x8193122cc04c3658 0x10326245980986cb 0x23b3303cc01c7e3c 0x4476660798038fc7

def z345 : W := mkw 0x00010120406030c0 0x00002024080c0618 0x80030320c06071c2 0xf0006064180c0e38

def z346 : W := mkw 0x3ffaba9aa31a0c00 0xc7ff575354634180 0x7fb0301c039c0e04 0x0ff60603807381c0

def z347 : W := mkw 0x0117400008496400 0x0022e80001092c80 0xa3ffc0000c7ffe07 0xd47ff800018fffc0

def z348 : W := mkw 0x0000002400001248 0x0000000480000249 0x0030003c00007e00 0x4006000780000fc0

def z349 : W := mkw 0x76c03ff706b693f8 0x2ed807fee0d6d27f 0xffc03fff0fff81ff 0xbff807ffe1fff03f

def z350 : W := mkw 0x0000042104001140 0x0000008420800228 0x00000c23000001c0 0x2000018460000038

def z351 : W := mkw 0x482c04370d805b68 0x09058086e1b00b6d 0xa03c003f0f807ff8 0x54078007e1f00fff

def z352 : W := mkw 0x81975769dc6df5d4 0x1032eaed3b8dbeba 0x83cfcfe3fc7ff1c3 0xf079f9fc7f8ffe38

def z353 : W := mkw 0x8193176cc46cb7d8 0x103262ed988d96fb 0xa3f33ffccc7fffff 0xf47e67ff998fffff

def z354 : W := mkw 0x81931328c06c34d0 0x10326265180d869a 0x83830320c07c71c2 0xf0706064180f8e38

def z355 : W := mkw 0x5ffebe9bad804920 0x8bffd7d375b00924 0x5fffffffff800007 0xebfffffffff00000

def z356 : W := mkw 0x36c13fe046f6b1f0 0x26d827fc08ded63e 0xffc33fe0cffff1ff 0xfff867fc19fffe3f

def z357 : W := mkw 0x44042c250d805b68 0x08808584a1b00b6d 0xfc003c000f807fff 0x3f80078001f00fff

def z358 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fcfcfc3f0000001 0x8bf9f9f87e000000

def z359 : W := mkw 0x3b7fc4210f5b7d40 0x476ff88421eb6fa8 0xffffcc230fffffc7 0xfffff98461fffff8

def z360 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0x5fc00fc00fff8001 0x8bf801f801fff000

def z361 : W := mkw 0x4c2c283709805a68 0x09858506e1300b4d 0x7c3c303f03807e3c 0x4f878607e0700fc7

def z362 : W := mkw 0x32c557e15e77f1d4 0x2658aafc2bcefe3a 0x83cfcfe3fc7ff1c3 0xf079f9fc7f8ffe38

def z363 : W := mkw 0x13d29288a0000000 0x827a525114000000 0x03f3f3fcf0000006 0xe07e7e7f9e000000

def z364 : W := mkw 0x36c03fdaa6b681b0 0xa6d807fb54d6d036 0xffc03fffffff81ff 0xbff807fffffff03f

def z365 : W := mkw 0x0113000000482400 0x0022600000090480 0x03830000007c0000 0x80706000000f8000

def z366 : W := mkw 0x3ffefa9aab134800 0xc7ffdf5355626900 0x5fffffffff838007 0xebfffffffff07000

def z367 : W := mkw 0x8197532cc86d76d8 0x1032ea65990daedb 0xa3fff33ccc7fffff 0xf47ffe67998fffff

def z368 : W := mkw 0x4cac3ebfad805b68 0x899587d7f5b00b6d 0xfc3c3fffff807fff 0x7f8787fffff00fff

def z369 : W := mkw 0x1ffababea0001248 0x83ff5757d4000249 0xfffffffff0007fff 0xfffffffffe000fff

def z370 : W := mkw 0x8197532dd86d76dc 0x1032ea65bb0daedb 0xa3bff33ff07c7ffe 0xf477fe67fe0f8fff

def z371 : W := mkw 0x3b7ec0000b1b4c00 0x476fd80001636980 0x7ffcc0000f9f8e05 0x0fff980001f3f1c0

def z372 : W := mkw 0x0828001200000000 0x0105000240000000 0x003c003f00000000 0x40078007e0000000

def z373 : W := mkw 0x20014000025b2400 0x44002800004b6480 0x00000000007f8000 0x00000000000ff000

def z374 : W := mkw 0x1ffebebbac005140 0x83ffd7d775800a28 0xdffffffffc0071c7 0xfbffffffff800e38

def z375 : W := mkw 0x3640288002920020 0x26c8051000524004 0x5c00000003800000 0x0b80000000700000

def z376 : W := mkw 0x000545415c61e184 0x0000a8a82b8c3c30 0x004fcfc3fc638001 0x8009f9f87f8c7000

def z377 : W := mkw 0x7ee83fd607b68bb8 0x2fdd07fac0f6d177 0xfff03fdc0fff8fff 0xbffe07fb81fff1ff

def z378 : W := mkw 0x09ba921aa0000000 0x8137524354000000 0x03bff33ff0000006 0xe077fe67fe000000

def z379 : W := mkw 0x3ffaba9aa31a0c00 0xc7ff575354634180 0x7ffffffff39c0e07 0xeffffffffe7381c0

def z380 : W := mkw 0x00801288a0000000 0x8010025114000000 0x000003c0f0000000 0x000000781e000000

def z381 : W := mkw 0x0400280000800020 0x0080050000100004 0x7c0030000380003c 0x0f80060000700007

def z382 : W := mkw 0x4c2c2c170d804b28 0x09858582e1b00965 0x7c3c3c1f0f800e3d 0x0f878783e1f001c7

def z383 : W := mkw 0x0080120000000000 0x0010024000000000 0x0380330000000006 0xa070066000000000

def z384 : W := mkw 0x81130008c0482400 0x1022600118090480 0x00030000c0000000 0x0000600018000000

def z385 : W := mkw 0x000444611c01d144 0x0000888c23803a28 0x804ccce33c03f1c3 0x7009999c67807e38

def z386 : W := mkw 0x3353c140527ba484 0x466a78280a4f7490 0x03c3c3c0f07f8000 0x807878781e0ff000

def z387 : W := mkw 0x3a6dc0000b536800 0x474db800016a6d00 0xdc4fc0000fe3f003 0xdb89f80001fc7e00

def z388 : W := mkw 0x44803ff704a493f8 0x289007fee094927f 0x00003fff000001f8 0x200007ffe000003f

def z389 : W := mkw 0xb3d3d308c27f2490 0x567a7a61184fe492 0x03c3c300c07f8000 0x80787860180ff000

def z390 : W := mkw 0x4dbe3e3f8d805b68 0x09b7c7c7f1b00b6d 0xffbf3f3fcf807fff 0xfff7e7e7f9f00fff

def z391 : W := mkw 0x80000004000c0618 0x10000000800180c3 0x20000000001c0e38 0x04000000000381c7

def z392 : W := mkw 0x16c03fc004a481b0 0x22d807f800949036 0x5fc03fc0000001ff 0xabf807f80000003f

def z393 : W := mkw 0x16c03e8004800120 0x02d807d000900024 0xffc03fc00f8001ff 0xbff807f801f0003f

def z394 : W := mkw 0x600544250fdb7f68 0x4c00a884a1fb6fed 0xa00000000ffffff8 0x1400000001ffffff

def z395 : W := mkw 0x04803fc004a481b0 0x209007f800949036 0xfc003fc00f8001ff 0x3f8007f801f0003f

def z396 : W := mkw 0x0004400118014004 0x0000880023002800 0x000cc00330000000 0x0001980066000000

def z397 : W := mkw 0x0112000000080400 0x0022400000010080 0x23b00000001c0e04 0x04760000000381c0

def z398 : W := mkw 0x3e68acd226928120 0xa7cd159a44d25024 0x5c4cccc33f838001 0x0b89999867f07000

def z399 : W := mkw 0x36c03bc002b680b0 0x26d807780056d016 0x7fc033c003ff803c 0x8ff80678007ff007

def z400 : W := mkw 0x7f7fe8160bdb6e28 0x4feffd02c17b6dc5 0xfffff01c0ffffe3f 0xdffffe0381ffffc7

def z401 : W := mkw 0x89bfd32cc96d7ed8 0x5137fa65992dafdb 0xa3bff33cc07c7ffe 0xf477fe67980f8fff

def z402 : W := mkw 0x324000c002128000 0x2648001800425000 0x004000c000038000 0x0008001800007000

def z403 : W := mkw 0x00000561542091c4 0x000000ac2a841238 0x004fcfe3f00001c3 0xe009f9fc7e000038

def z404 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0x03b3033cc07c7e00 0xc0766067980f8fc0

def z405 : W := mkw 0x3eec3fc00fb6c9b0 0x27dd87f801f6d936 0xfffc3fc00fffffff 0xffff87f801ffffff

def z406 : W := mkw 0x04803fc004a481b0 0x209007f800949036 0x80403fc00c6381fb 0xb00807f8018c703f

def z407 : W := mkw 0x1ffefedbbc01c104 0x83ffdfdb77803820 0x5ffffffffc038007 0xebffffffff807000

def z408 : W := mkw 0x85933bbee06c36d8 0x90b26777dc0d86db 0xa3b33ffff07c7ffe 0xf47667fffe0f8fff

def z409 : W := mkw 0x20000000031a0c00 0x4400000000634180 0x20000000039c0e00 0x04000000007381c0

def z410 : W := mkw 0x0005400008416000 0x0000a80001082c00 0x800000000c63f000 0x10000000018c7e00

def z411 : W := mkw 0x3353c000025b2400 0x466a7800004b6480 0xffc3c0000fff8007 0x9ff8780001fff000

def z412 : W := mkw 0x5ffabebfa4801368 0x8bff57d7f490026d 0x5ffffffff00001ff 0xebfffffffe00003f

def z413 : W := mkw 0x01130120406834c0 0x00226024080d0698 0xa3b30320c07c7fc6 0xf4766064180f8ff8

def z414 : W := mkw 0x16c57fe15c61f1c4 0x02d8affc2b8c3e38 0xdfcfffe3fc63f1c7 0xfbf9fffc7f8c7e38

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0xa3800000007c0006 0x94700000000f8000

def z416 : W := mkw 0x200545615f7bfdc4 0x4400a8ac2bef7fb8 0xa00000000fffffc0 0x1400000001fffff8

def z417 : W := mkw 0x1b7fc00009496c00 0x436ff80001292d80 0x5fffc00000007e07 0xcbfff80000000fc0

def z418 : W := mkw 0x093fc00009496c00 0x4127f80001292d80 0xfc3fc0000f807e07 0x5f87f80001f00fc0

def z419 : W := mkw 0x482c001309004800 0x0905800261200900 0x000c000300000000 0x0001800060000000

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x0043c3c0f0000000 0x800878781e000000

def z421 : W := mkw 0x0c28281200000000 0x0185050240000000 0x5c7ffffff0000007 0xeb8ffffffe000000

def z422 : W := mkw 0x082d400009416800 0x0105a80001282d00 0xfc7fc0000fe3fe07 0xdf8ff80001fc7fc0

def z423 : W := mkw 0x81130124406c36d8 0x10226024880d86db 0xa3b30000007c7ffe 0xd4766000000f8fff

def z424 : W := mkw 0x1b7e800009004800 0x036fd00001200900 0xffffc0000f807e07 0xdffff80001f00fc0

def z425 : W := mkw 0x3bffd2088b5b6c00 0x477ffa41116b6d80 0xfffff33ccffffe07 0xfffffe6799ffffc0

def z426 : W := mkw 0x0000000000000000 0x0000000000000000 0x00030320c0000002 0xe000606418000000

def z427 : W := mkw 0x4c28281601800a28 0x09850502c0300145 0x7c3c3c3f03800e3f 0x6f878787e07001c7

def z428 : W := mkw 0x0080120000040010 0x0010024000008002 0x23803000001c003c 0x0470060000038007

def z429 : W := mkw 0x7ffffebfafdb7f68 0xcfffffd7f5fb6fed 0xffffffffffffffff 0xffffffffffffffff

def z430 : W := mkw 0x4c282c3704801368 0x09850586e090026d 0x5c3c3c3f000001ff 0x6b878787e000003f

def z431 : W := mkw 0x000105604460b1c0 0x000020ac088c1638 0x80430fe0cc63f1c3 0xf00861fc198c7e38

def z432 : W := mkw 0x1ee8ba9220000000 0x83dd175244000000 0x5fccffc330000007 0xabf99ff866000000

def z433 : W := mkw 0xc5933f3fc4ec37f8 0x18b267e7f89d86ff 0xa3b33f3fc07c7ffe 0xf47667e7f80f8fff

def z434 : W := mkw 0x8001002440483648 0x10002004880906c9 0x0000000000007e00 0x0000000000000fc0

def z435 : W := mkw 0x1bfa9288a0000000 0x837f525114000000 0x5fffc3c0f0000007 0xcbfff8781e000000

def z436 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3830300c07c7ff8 0x94706060180f8fff

def z437 : W := mkw 0x082d45615d61f9c4 0x0105a8ac2bac3f38 0xfc7fcfe3ffe3ffc7 0xff8ff9fc7ffc7ff8

def z438 : W := mkw 0x1ffbbbbae06030c0 0x83ff77775c0c0618 0xdffffffff06071c7 0xfbfffffffe0c0e38

def z439 : W := mkw 0x000541615861f0c4 0x0000a82c2b0c3e18 0x004fc3e3f063f000 0xc009f87c7e0c7e00

def z440 : W := mkw 0x4d3f2c370dc87f68 0x09a7e586e1b90fed 0xffbf3c3f0ffc7fff 0xfff7e787e1ff8fff

def z441 : W := mkw 0x482c04370d005b48 0x09058086e1a00b69 0x803c0c3f0c007fc3 0x70078187e1800ff8

def z442 : W := mkw 0x3ee8bfd226b681b0 0xa7dd17fa44d6d036 0xffccffc33fff81ff 0xbff99ff867fff03f

def z443 : W := mkw 0x4c2c2c130d804920 0x0985858261b00924 0xfc0c3c030f8001ff 0x3f81878061f0003f

def z444 : W := mkw 0x04803fc004a481b0 0x209007f800949036 0xa3803fc0007c01fe 0xb47007f8000f803f

def z445 : W := mkw 0x4c2c2d770da0dbe8 0x098585aee1b41b7d 0xfc7c3fff0fe3ffff 0xff8f87ffe1fc7fff

def z446 : W := mkw 0x0000040004800120 0x0000008000900024 0xa00000000f8001f8 0x1400000001f0003f

def z447 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x8043c3c0fc63f1c0 0x900878781f8c7e38

def z448 : W := mkw 0x0080130000240090 0x0010026000048012 0x03800300007c0000 0x80700060000f8000

def z449 : W := mkw 0x093fc00009496c00 0x4127f80001292d80 0x807fc0000c63fe03 0xd00ff800018c7fc0

def z450 : W := mkw 0x00801324002412d8 0x001002648004825b 0xa3b0333c007c7ffe 0xf4760667800f8fff

def z451 : W := mkw 0xb7d23a8c829e0638 0x36fa47519053c0c7 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z452 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x80030320cc63f1c2 0xf0006064198c7e38

def z453 : W := mkw 0x000544215c417144 0x0000a8842b882e28 0x800fcc23fc0071c3 0x7001f9847f800e38

def z454 : W := mkw 0x1b7fc00008416000 0x036ff80001082c00 0xdfffc0000c63f007 0xdbfff800018c7e00

def z455 : W := mkw 0x1e6cecd33c01c104 0x83cd9d9a67803820 0x5c4cccc33c038001 0x0b89999867807000

def z456 : W := mkw 0x093fc5615d69fdc4 0x4127f8ac2bad3fb8 0x807fcfe3fc63ffc3 0xf00ff9fc7f8c7ff8

def z457 : W := mkw 0x1ffabe9aa4800120 0x83ff57d354900024 0xffffffffff8001ff 0xfffffffffff0003f

def z458 : W := mkw 0x01128008a0000000 0x8022500114000000 0x0003c000f0000000 0x000078001e000000

def z459 : W := mkw 0x1b7fc5615c61f1c4 0x036ff8ac2b8c3e38 0xdfffcfe3fc63f1c7 0xfbfff9fc7f8c7e38

def z460 : W := mkw 0x0c28281200000000 0x0185050240000000 0x5c30301c00000004 0x0b86060380000000

def z461 : W := mkw 0xbbffd20c8b5f6e18 0x577ffa41916bedc3 0xfffff01c0ffffe3f 0xdffffe0381ffffc7

def z462 : W := mkw 0x36c03a8002120000 0x06d8075000424000 0xffc03fc00fff8007 0xbff807f801fff000

def z463 : W := mkw 0x7ffffff70ffffff8 0x6ffffffee1ffffff 0xffffffff0fffffff 0xffffffffe1ffffff

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x004fc00000000003 0xc009f80000000000

def z465 : W := mkw 0x16c03a9aa0000000 0x82d8075354000000 0x5fc03ffff0000007 0xabf807fffe000000

def z466 : W := mkw 0xc9bf133fc96c7ed8 0x1937e267f92d8fdb 0xa3bf333fc07c7ffe 0xf477e667f80f8fff

def z467 : W := mkw 0x000145615461b1c4 0x000028ac2a8c3638 0x0043cfe3f06381c0 0xa00879fc7e0c7038

def z468 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fb03ffff0000004 0x2bf607fffe000000

def z469 : W := mkw 0x04002cc004808120 0x2080059800901024 0x00000cc000000000 0x0000019800000000

def z470 : W := mkw 0x80801308c0240090 0x1010026118048012 0x00000300c0000000 0x0000006018000000

def z471 : W := mkw 0x00010120406030c0 0x00002024080c0618 0x80000000006071c0 0x10000000000c0e38

def z472 : W := mkw 0x5eec3eb70d805b68 0x0bdd87d6e1b00b6d 0xfffc3fff0f807fff 0xffff87ffe1f00fff

def z473 : W := mkw 0x16c03a8000000000 0x02d8075000000000 0x5fcfffe3f0000007 0xebf9fffc7e000000

def z474 : W := mkw 0x093fc57bfc61f1c4 0x8127f8af7f8c3e38 0x807fcffffc63f1c3 0xf00ff9ffff8c7e38

def z475 : W := mkw 0x093fc00009496c00 0x4127f80001292d80 0xa3bfc000007c7e06 0xd477f800000f8fc0

def z476 : W := mkw 0x1e6dedf37c61f1c4 0x83cdbdbe6f8c3e38 0xdc4fcfe3fc63f1c3 0xfb89f9fc7f8c7e38

def z477 : W := mkw 0x5e6cacb72d805b68 0x8bcd9596e5b00b6d 0xfc7cfcff3f807fff 0x7f8f9f9fe7f00fff

def z478 : W := mkw 0x3a6cc0000b134800 0x474d980001626900 0xfc7cc0000f83fe07 0x5f8f980001f07fc0

def z479 : W := mkw 0x3b7b8000035a2c00 0x476f7000006b4580 0xffb3000003fc7e06 0xdff66000007f8fc0

def z480 : W := mkw 0x1352800000000000 0x026a500000000000 0x03c3c00000000000 0x8078780000000000

def z481 : W := mkw 0x1ffffa9aa8416000 0x83ffff5355082c00 0xdffffffffc63f007 0xfbffffffff8c7e00

def z482 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x804fc0000c63f1c3 0xd009f800018c7e38

def z483 : W := mkw 0x8117456ddc69f7cc 0x1022e8adbb8d3ef9 0x807fcffffc63ffc3 0xf00ff9ffff8c7ff8

def z484 : W := mkw 0x3240000002120000 0x0648000000424000 0x7f800000039c0004 0x0ff0000000738000

def z485 : W := mkw 0x000405610c20d1c0 0x000080ac21841a38 0x804c0fe30c63f1c3 0xf00981fc618c7e38

def z486 : W := mkw 0x4c2c2d775da0dbec 0x098585aeebb41b7d 0xfc3c3fffff807fff 0x7f8787fffff00fff

def z487 : W := mkw 0x0080174004248190 0x001002e800849032 0xa3c03fc00c7f81ff 0xb47807f8018ff03f

def z488 : W := mkw 0x8113012cc06c36d8 0x10226025980d86db 0xa033003cc07c7ff8 0x54066007980f8fff

def z489 : W := mkw 0x36c57fc00fffedb0 0x66d8aff801fffdb6 0xffc03fc00fffffff 0xbff807f801ffffff

def z490 : W := mkw 0x211740000b5b6c00 0x4422e800016b6d80 0xa3b300000ffffe06 0xd476600001ffffc0

def z491 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fb3333cc0000006 0xebf6666798000000

def z492 : W := mkw 0x400404250d805b68 0x08008084a1b00b6d 0xa030303c0f807ffe 0x7406060781f00fff

def z493 : W := mkw 0x000445615c21d1c4 0x000088ac2b843a38 0x004ccfe3fc0381c1 0x200999fc7f807038

def z494 : W := mkw 0x3bffd288ab5b6c00 0xc77ffa51156b6d80 0xffffc3c0fffffe07 0xdffff8781fffffc0

def z495 : W := mkw 0x3b7a8000031a0c00 0x476f500000634180 0x7fffc000039c0e07 0xcffff800007381c0

def z496 : W := mkw 0x04803fdaa4a481b0 0xa09007fb54949036 0x00003ffff00001f8 0x200007fffe00003f

def z497 : W := mkw 0xb7d33fc8c6fea5b0 0x36fa67f918dfd4b6 0xffc33fc0cfff81ff 0xbff867f819fff03f

def z498 : W := mkw 0x0000014050208084 0x000000280a041010 0x000003c0f0000000 0x000000781e000000

def z499 : W := mkw 0x5f7eac370d805b68 0x0befd586e1b00b6d 0xfffffc3f0f807fff 0xffffff87e1f00fff

def z500 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0x5c0c3c3f0f8001f9 0x2b818787e1f0003f

def z501 : W := mkw 0x05923a9aa0000000 0x80b2475354000000 0x03b33ffff0000006 0xe07667fffe000000

def z502 : W := mkw 0x3357c0000a5b6400 0x466af800014b6c80 0x83cfc0000c7ff003 0xd079f800018ffe00

def z503 : W := mkw 0x000145405461a184 0x000028a80a8c3430 0x8043cfc0fc6381c3 0xb00879f81f8c7038

def z504 : W := mkw 0x0005400008416000 0x0000a80001082c00 0x000fc00000007000 0x4001f80000000e00

def z505 : W := mkw 0x3a6cc0000b134800 0x474d980001626900 0xffccc0000fff8007 0x9ff9980001fff000

def z506 : W := mkw 0x32c013c002368090 0x265802780046d012 0xffc003c00fff8007 0x9ff8007801fff000

def z507 : W := mkw 0xcdbf7f7fddedfffc 0x19b7efeffbbdbfff 0xffffffffffffffff 0xffffffffffffffff

def z508 : W := mkw 0x4400281600800228 0x08800502c0100045 0x0000301c00000038 0x0000060380000007

def z509 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fbc3c3f00000007 0x6bf78787e0000000

def z510 : W := mkw 0x44042c370d805b68 0x08808586e1b00b6d 0xa0003c3f0f807ff8 0x34000787e1f00fff

def z511 : W := mkw 0x4000003700001248 0x08000006e0000249 0x0000003f00000000 0x00000007e0000000

def z512 : W := mkw 0x1b7a800000000000 0x036f500000000000 0x5fffcfe3f0000007 0xebfff9fc7e000000

def z513 : W := mkw 0x1ffabfdaa4208180 0x83ff57fb54841030 0xdffffffffc6381c7 0xfbffffffff8c7038

def z514 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0x7f803fc0039c01fc 0x2ff007f80073803f

def z515 : W := mkw 0xb6c03fecc6b693f8 0x36d807fd98d6d27f 0xffc03ffccfff81ff 0xbff807ff99fff03f

def z516 : W := mkw 0x3ffffffbfef7f1f4 0xa7ffffff7fdefe3e 0xfffffffffffff1ff 0xfffffffffffffe3f

def z517 : W := mkw 0x3b7fc5400f7bed80 0x476ff8a801ef7db0 0xffffcfc00fffffc7 0xfffff9f801fffff8

def z518 : W := mkw 0x8080120c80040218 0x1010024190008043 0x0000301c00000038 0x0000060380000007

def z519 : W := mkw 0x80010100406c2490 0x10002020080d8492 0x00000000007c0000 0x00000000000f8000

def z520 : W := mkw 0x36402cc006928120 0x26c8059800d25024 0xffc00cc00fff8007 0x9ff8019801fff000

def z521 : W := mkw 0x85933fecc4ecb7f8 0x30b267fd989d96ff 0xa3b33ffcc07c7ffe 0xf47667ff980f8fff

def z522 : W := mkw 0x4cac3f370da45bf8 0x099587e6e1b48b7f 0xffbc3f3f0ffc7fff 0xfff787e7e1ff8fff

def z523 : W := mkw 0x37d33fc006fea5b0 0x26fa67f800dfd4b6 0xfff33fc00fffffff 0xfffe67f801ffffff

def z524 : W := mkw 0x13d3d3c8f061a084 0x827a7a791e0c3410 0x03c3c3c0f0638000 0x807878781e0c7000

def z525 : W := mkw 0x9ffbbbbee06c36d8 0x93ff7777dc0d86db 0xffb3333cc07c7ffe 0xfff66667980f8fff

def z526 : W := mkw 0x44803ebfa4801368 0x889007d7f490026d 0x00003ffff00001f8 0x200007fffe00003f

def z527 : W := mkw 0x3a6cc4411f13c904 0x474d988823e27920 0x5c4cccc33f838001 0x0b89999867f07000

def z528 : W := mkw 0x44002c3704801368 0x08800586e090026d 0xfc003c3f0f8001ff 0x3f800787e1f0003f

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x000fc023f0000000 0x4001f8047e000000

def z530 : W := mkw 0x36c03ec006968130 0x26d807d800d2d026 0x7fc03cc00f9f803d 0x0ff8079801f3f007

def z531 : W := mkw 0x000404250c005348 0x00008084a1800a69 0xa03c3c3f0c007fff 0x74078787e1800fff

def z532 : W := mkw 0x1e68a89220000000 0x83cd151244000000 0x5c4fcfe3f0000003 0xeb89f9fc7e000000

def z533 : W := mkw 0x093fc01aa9496c00 0xc127f80355292d80 0x003fc03ff0007e00 0x4007f807fe000fc0

def z534 : W := mkw 0x1ffeba9aa9004800 0x83ffd75355200900 0xffffffffff807e07 0xfffffffffff00fc0

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z536 : W := mkw 0x81935348d06da494 0x10326a691a0db492 0x03c3c3c0f07f8000 0x807878781e0ff000

def z537 : W := mkw 0x76c43fe50fb6dbf8 0x2ed887fca1f6db7f 0xffc03fc00fffffff 0xbff807f801ffffff

def z538 : W := mkw 0x1ffabffbf42091c4 0x83ff57ff7e841238 0x5ffffffff00001c7 0xebfffffffe000038

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0003000000001fe 0x340006000000003f

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x804000000c638003 0x90080000018c7000

def z541 : W := mkw 0x9ffabbbee02412d8 0x93ff5777dc04825b 0x5ffffffff00001ff 0xebfffffffe00003f

def z542 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5ff03fdc00000007 0xabfe07fb80000000

def z543 : W := mkw 0x3b7a800002120000 0x076f500000424000 0xffffc0000fff8007 0xdffff80001fff000

def z544 : W := mkw 0x33d3d3c0027fa490 0x667a7a78004ff492 0x03c3c3c0007f8000 0x80787878000ff000

def z545 : W := mkw 0x00054120486170c0 0x0000a824090c2e18 0x804fc320cc63f1c3 0xf009f864198c7e38

def z546 : W := mkw 0x9ffffffffc6df7dc 0x93ffffffff8dbefb 0xfffffffffc7fffff 0xffffffffff8fffff

def z547 : W := mkw 0x32c153c05277a094 0x26582a780a4ef412 0x03c3c3c0f07f8000 0x807878781e0ff000

def z548 : W := mkw 0x0004400008014000 0x0000880001002800 0x004cc0000c038001 0x0009980001807000

def z549 : W := mkw 0x36c57fe15ef7f1f4 0x26d8affc2bdefe3e 0xffc03fc00ffff1ff 0xbff807f801fffe3f

def z550 : W := mkw 0x4c2d6c370dc17b68 0x0985ad86e1b82f6d 0xfc7ffc3f0fe3ffff 0xff8fff87e1fc7fff

def z551 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x800fc023fc63f1c0 0x5001f8047f8c7e38

def z552 : W := mkw 0x000505214c6071c0 0x0000a0a4298c0e38 0x800f0f23cc6071c3 0xf001e1e4798c0e38

def z553 : W := mkw 0xbbfb932cc37e3ed8 0x577f7265986fc7db 0xffb3333cc3fc7ffe 0xfff66667987f8fff

def z554 : W := mkw 0x000404010c004100 0x0000808021800820 0x000c0c030c000001 0x0001818061800000

def z555 : W := mkw 0x6c2d6c370fdb7f68 0x4d85ad86e1fb6fed 0xfc3c3c3f0fffffff 0x7f878787e1ffffff

def z556 : W := mkw 0x36456de15ef3f1e4 0x26c8adbc2bde7e3c 0xdc4fcfe3ffe3f1c3 0xfb89f9fc7ffc7e38

def z557 : W := mkw 0x7f7fed775ffbffec 0x4feffdaeebff7ffd 0xffffffffffffffff 0xffffffffffffffff

def z558 : W := mkw 0x4c2c281609804a28 0x09858502c1300945 0xfc3c301c0f807e3f 0x5f87860381f00fc7

def z559 : W := mkw 0x1240808020000000 0x8248101004000000 0x0040c0c030000000 0x0008181806000000

def z560 : W := mkw 0x7b7fc4250fdb7f68 0x4f6ff884a1fb6fed 0xffffc0000fffffff 0xdffff80001ffffff

def z561 : W := mkw 0x1ffaba8000000000 0x03ff575000000000 0x5fffffc000000007 0xebfffff800000000

def z562 : W := mkw 0x482c003709005a48 0x09058006e1200b49 0xfc3c003f0f807e07 0x5f878007e1f00fc0

def z563 : W := mkw 0x36c03ec006928120 0x26d807d800d25024 0x5fc03fc00f838007 0xabf807f801f07000

def z564 : W := mkw 0x000445411c21c184 0x000088a823843830 0x804ccfc33c6381c3 0xb00999f8678c7038

def z565 : W := mkw 0x3a6dc5615f73f9c4 0x474db8ac2bee7f38 0xdc4fcfe3ffe3f1c3 0xfb89f9fc7ffc7e38

def z566 : W := mkw 0x3357c0000b5b6c00 0x466af800016b6d80 0xa3c3c0000ffffe00 0x9478780001ffffc0

def z567 : W := mkw 0x8000002cc0001248 0x1000000598000249 0x0000003cc0000000 0x0000000798000000

def z568 : W := mkw 0x4cac3ff70da4dbf8 0x299587fee1b49b7f 0xfc3c3fff0f807fff 0x7f8787ffe1f00fff

def z569 : W := mkw 0x1bfa929aa0000000 0x837f525354000000 0x03ffc3fff0000000 0xc07ff87ffe000000

def z570 : W := mkw 0x3a68800003120800 0x474d100000624100 0x5c00000003800000 0x0b80000000700000

def z571 : W := mkw 0x81931308c06c2490 0x10326261180d8492 0x03b3333cc07c0006 0xe0766667980f8000

def z572 : W := mkw 0x12c0128000000000 0x0258025000000000 0x03c003c000000000 0x8078007800000000

def z573 : W := mkw 0x282d40000b5b6c00 0x4505a800016b6d80 0xfc3c00000ffffe07 0x5f87800001ffffc0

def z574 : W := mkw 0x008013c000248090 0x2010027800049012 0x000003c000000000 0x0000007800000000

def z575 : W := mkw 0x00000120402010c0 0x0000002408040218 0x00000320c00001c0 0x2000006418000038

def z576 : W := mkw 0x3bffd3c00b7fec90 0x677ffa78016ffd92 0xffffc3c00ffffe07 0xdffff87801ffffc0

def z577 : W := mkw 0xbbffd76ddf7fffdc 0x577ffaedbbeffffb 0xffffffffffffffff 0xffffffffffffffff

def z578 : W := mkw 0x0828801220000000 0x8105100244000000 0x000cc00330000000 0x0001980066000000

def z579 : W := mkw 0x32c017c006b681b0 0x265802f800d6d036 0xa3c003c00fff81f8 0x9478007801fff03f

def z580 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0x7fbfc000039c7e04 0x4ff7f80000738fc0

def z581 : W := mkw 0x0c2c2c330c005140 0x0185858661800a28 0xdc3c3c3f0c0071c7 0x7b878787e1800e38

def z582 : W := mkw 0x3b7bc000025b2400 0x476f7800004b6480 0x5fffc000007f8007 0xcbfff800000ff000

def z583 : W := mkw 0x0c2c2c000d804920 0x0185858001b00924 0xfc3c3c000f807fff 0x7f87878001f00fff

def z584 : W := mkw 0x3240054006328180 0x064800a800c65030 0xffc00fc00fff81c7 0xbff801f801fff038

def z585 : W := mkw 0x4c2c6c531d81c924 0x09858d8a63b03924 0x5c4cccc33f838001 0x0b89999867f07000

def z586 : W := mkw 0x01975769dc61f1c4 0x0032eaed3b8c3e38 0x83fffffffc63f1c7 0xf07fffffff8c7e38

def z587 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0x03ffc000007ffe00 0xc07ff800000fffc0

def z588 : W := mkw 0x44056d775ce1f3ec 0x0880adaeeb9c3e7d 0x804ffffffc63f1fb 0xf009ffffff8c7e3f

def z589 : W := mkw 0x1f7aa89220000000 0x83ef551244000000 0x5fffccc330000007 0xcbfff99866000000

def z590 : W := mkw 0x0000010000240090 0x0000002000048012 0xa0000000007c01f8 0x14000000000f803f

def z591 : W := mkw 0x082cc00009014800 0x4105980001202900 0x000cc00000000000 0x0001980000000000

def z592 : W := mkw 0x81931308c06c2490 0x10326261180d8492 0xa3833300c07c01fe 0xb4706660180f803f

def z593 : W := mkw 0x4c2d6c375dc17b6c 0x0985ad86ebb82f6d 0xfc3ffc3fff807fff 0x7f87ff87fff00fff

def z594 : W := mkw 0x0d3aa81aa0000000 0x81a7550354000000 0x5c3ffc3ff0000007 0x6b87ff87fe000000

def z595 : W := mkw 0x082c04210d005940 0x0105808421a00b28 0xfc3c0c230f807fc7 0x7f87818461f00ff8

def z596 : W := mkw 0x200545615f7bfdc4 0x4400a8ac2bef7fb8 0xa04fcfe3ffffffc3 0xf409f9fc7ffffff8

def z597 : W := mkw 0x3e6ce8922b134800 0xc7cd9d1245626900 0x5c4cccc33f838001 0x0b89999867f07000

def z598 : W := mkw 0x0000044004008100 0x0000008800801020 0x00400cc00c038001 0x0008019801807000

def z599 : W := mkw 0x04857ffbfc61f1c4 0x8090afff7f8c3e38 0x804ffffffc63f1c3 0xf009ffffff8c7e38

def z600 : W := mkw 0x8192120c800c0618 0x10324241900180c3 0x23b3333cc01c0e3e 0xe4766667980381c7

def z601 : W := mkw 0x04002d4004a081a0 0x008005a800941034 0xfc403fc00fe381ff 0xbf8807f801fc703f

def z602 : W := mkw 0x0005402158417044 0x0000a8042b082e08 0x804fc023fc63f003 0xd009f8047f8c7e00

def z603 : W := mkw 0x0dba3a1a80000000 0x01b7474350000000 0x5fbf3f3fc0000007 0xebf7e7e7f8000000

def z604 : W := mkw 0x400404250d805b68 0x08008084a1b00b6d 0xa00c0c230f807ffb 0x7401818461f00fff

def z605 : W := mkw 0x36c47fc11eb7c1b4 0x26d88ff823d6f836 0xffccffc33fff81ff 0xbff99ff867fff03f

def z606 : W := mkw 0x4c282c3705801b68 0x09850586e0b0036d 0x7c303c3f03800ffc 0x2f860787e07001ff

def z607 : W := mkw 0x0000054004a481b0 0x200000a800949036 0x00000000000001f8 0x000000000000003f

def z608 : W := mkw 0x37d2bfc8a6b681b0 0xa6fa57f914d6d036 0xffc3ffc0ffff81ff 0xbff87ff81ffff03f

def z609 : W := mkw 0x3240000002120000 0x0648000000424000 0x03c00000007f8000 0x80780000000ff000

def z610 : W := mkw 0x44002c1304800120 0x0880058260900024 0x00000c0300000000 0x0000018060000000

def z611 : W := mkw 0x7e6cec370f935b68 0x4fcd9d86e1f26b6d 0xfc7cfc3f0f83ffff 0x7f8f9f87e1f07fff

def z612 : W := mkw 0x01931300006c2490 0x00326260000d8492 0xa3b33300007c7ffe 0xf4766660000f8fff

def z613 : W := mkw 0x000444411c01c104 0x0000888823803820 0x000000000c038000 0x0000000001807000

def z614 : W := mkw 0x4c2c283709005a48 0x09858506e1200b49 0x5c3c3c3f00007e07 0x6b878787e0000fc0

def z615 : W := mkw 0xcd3f2c3fcdc87f68 0x19a7e587f9b90fed 0xfc3f3c3fcf807fff 0x7f87e787f9f00fff

def z616 : W := mkw 0x8113012cc06836c8 0x10226025980d06d9 0x8033033cc0607fc2 0xf0066067980c0ff8

def z617 : W := mkw 0x04857fe15ce5f1f4 0x2090affc2b9cbe3e 0x804fffe3fc63f1fb 0xf009fffc7f8c7e3f

def z618 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fbff03ff0000004 0x4bf7fe07fe000000

def z619 : W := mkw 0x3b7bc000035b2c00 0x476f7800006b6580 0x7ff3c00003ff8e04 0x8ffe7800007ff1c0

def z620 : W := mkw 0x3b7fc1204b7b7cc0 0x476ff824096f6f98 0xffffc320cfffffc7 0xfffff86419fffff8

def z621 : W := mkw 0x9bfb932cc06c36d8 0x137f7265980d86db 0xfffff33cc07c7fff 0xfffffe67980f8fff

def z622 : W := mkw 0x1ee8ba9aa0000000 0x83dd175354000000 0x5c4cfffff0000001 0x2b899ffffe000000

def z623 : W := mkw 0x81921208800c0410 0x1032424110018082 0x03800000001c0000 0x0070000000038000

def z624 : W := mkw 0x200545400fffedb0 0x6400a8a801fffdb6 0xa00000000ffffff8 0x1400000001ffffff

def z625 : W := mkw 0xbb7fc02ccb5b7e48 0x576ff805996b6fc9 0xffffc03ccffffe07 0xdffff80799ffffc0

def z626 : W := mkw 0x16c03a8000000000 0x02d8075000000000 0x5f80300000000004 0x0bf0060000000000

def z627 : W := mkw 0x8192130c802c0698 0x10324261900580d3 0xa3b0331c007c0ffe 0xb4760663800f81ff

def z628 : W := mkw 0x0000002000001040 0x0000000400000208 0x80000020000071c2 0x7000000400000e38

def z629 : W := mkw 0x0193120880482400 0x0032624110090480 0xa3b3333cc07c7e06 0xf4766667980f8fc0

def z630 : W := mkw 0x1bfa920880000000 0x037f524110000000 0x5ffff33cc0000007 0xebfffe6798000000

def z631 : W := mkw 0x04002c0004800120 0x0080058000900024 0x00003c00000001f8 0x200007800000003f

def z632 : W := mkw 0x7f7fec130fdb6d20 0x4feffd8261fb6da4 0xffffcc030ffffe07 0xdffff98061ffffc0

def z633 : W := mkw 0x0000010000200080 0x0000002000040010 0x80000300006001c2 0xb0000060000c0038

def z634 : W := mkw 0x3ffabfdaa6b681b0 0xa7ff57fb54d6d036 0xfff03fdc0fff81ff 0xbffe07fb81fff03f

def z635 : W := mkw 0x5ffaba9ea1800a28 0x8bff5753d4300145 0x7fb0301c03800e3c 0x0ff60603807001c7

def z636 : W := mkw 0x13d7d7e9fc61f1c4 0x827afafd3f8c3e38 0x83cfcfe3fc63f1c3 0xf079f9fc7f8c7e38

def z637 : W := mkw 0x0113c00000492400 0x4022780000092480 0x0003c00000000000 0x0000780000000000

def z638 : W := mkw 0x0113000000482400 0x0022600000090480 0x0033000000007e00 0x4006600000000fc0

def z639 : W := mkw 0x0828000001000800 0x0105000000200100 0x7c30000003800e04 0x0f860000007001c0

def z640 : W := mkw 0x5ffaba9ea1800a28 0x8bff5753d4300145 0x7ffffffff3800e3f 0xeffffffffe7001c7

def z641 : W := mkw 0x3ffffa800b5b6c00 0x47ffff50016b6d80 0xffffffc00ffffe07 0xfffffff801ffffc0

def z642 : W := mkw 0x8193122cc0483648 0x10326245980906c9 0x03b3333cc0007e06 0xe076666798000fc0

def z643 : W := mkw 0x600405650fb6dbf8 0x2c0080aca1f6db7f 0xa00000000ffffff8 0x1400000001ffffff

def z644 : W := mkw 0x1ffabb9aa0240090 0x83ff577354048012 0xfffffffff07c01ff 0xfffffffffe0f803f

def z645 : W := mkw 0x3bffd3000b7f6c90 0x477ffa60016fed92 0xfffff3000fffffff 0xfffffe6001ffffff

def z646 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0x03c03fc0007f81f8 0xa07807f8000ff03f

def z647 : W := mkw 0x01931328c06030c0 0x00326265180c0618 0x83b3333cc06071c6 0xf0766667980c0e38

def z648 : W := mkw 0x5ffebebfad805b68 0x8bffd7d7f5b00b6d 0xffbc3c3f0f807fff 0x7ff78787e1f00fff

def z649 : W := mkw 0x8193130cc06c2698 0x10326261980d84d3 0x23b3331cc07c0e3c 0x84766663980f81c7

def z650 : W := mkw 0xbffbbffee6feb7f8 0xb7ff77ffdcdfd6ff 0xffffffffffffffff 0xffffffffffffffff

def z651 : W := mkw 0xdfffbfbfedec7ff8 0x9bfff7f7fdbd8fff 0xfffffffffffc7fff 0xffffffffffff8fff

def z652 : W := mkw 0xffffff3fcfff7ff8 0x5fffffe7f9ffefff 0xffffff3fcfffffff 0xffffffe7f9ffffff

def z653 : W := mkw 0x04803ffbf42091c4 0x809007ff7e841238 0x00003ffff00001c0 0x200007fffe000038

def z654 : W := mkw 0x1ffbfbdaf061a084 0x83ff7f7b5e0c3410 0x5ffffffff0638007 0xebfffffffe0c7000

def z655 : W := mkw 0xbbffd308cb7f6c90 0x577ffa61196fed92 0xffffc300cffffe07 0xdffff86019ffffc0

def z656 : W := mkw 0x36446cc11e93c124 0x26c88d9823d27824 0x5c4cccc33f838001 0x0b89999867f07000

def z657 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5ff3f3dcf0000004 0x8bfe7e7b9e000000

def z658 : W := mkw 0xcdbb3b3ec1ec3ef8 0x19b76767d83d87df 0xffb3333cc3fc7ffe 0xfff66667987f8fff

def z659 : W := mkw 0x3b7fc4411f5bed04 0x476ff88823eb7da0 0xffffccc33ffffe07 0xdffff99867ffffc0

def z660 : W := mkw 0x3fffffdaafffedb0 0xe7fffffb55fffdb6 0xffffffffffffffff 0xffffffffffffffff

def z661 : W := mkw 0x3b7ec0000b134800 0x476fd80001626900 0x5fffc0000f838007 0xcbfff80001f07000

def z662 : W := mkw 0x4c2c2c130d804920 0x0985858261b00924 0xfc3c0c030f807e07 0x5f87818061f00fc0

def z663 : W := mkw 0x33528000021a0400 0x466a500000434080 0x03800000001c0000 0x0070000000038000

def z664 : W := mkw 0x1b7a801aa0000000 0x836f500354000000 0x5fffc03ff0000007 0xcbfff807fe000000

def z665 : W := mkw 0x7ee83a9603960a38 0x2fdd0752c072c147 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z666 : W := mkw 0x093a800001080c00 0x4127500000210180 0x0030000000000e00 0x00060000000001c0

def z667 : W := mkw 0x1240000000000000 0x0248000000000000 0x5fc0000000000007 0x8bf8000000000000

def z668 : W := mkw 0x400404010d804920 0x0800808021b00924 0x000000000f800000 0x0000000001f00000

def z669 : W := mkw 0x324545615e73f1c4 0x0648a8ac2bce7e38 0xffcfcfe3fffff1c7 0xfff9f9fc7ffffe38

def z670 : W := mkw 0x000544615c41f144 0x0000a88c2b883e28 0x004fcce3fc03f001 0x4009f99c7f807e00

def z671 : W := mkw 0xccac3f3fcda45bf8 0x199587e7f9b48b7f 0xfc3c3f3fcf807fff 0x7f8787e7f9f00fff

def z672 : W := mkw 0x04803a8000000000 0x0090075000000000 0x00003fc000000000 0x200007f800000000

def z673 : W := mkw 0x0000002400001248 0x0000000480000249 0xa000000000007ff8 0x1400000000000fff

def z674 : W := mkw 0x1b7a800000000000 0x036f500000000000 0x5fb0000000000004 0x0bf6000000000000

def z675 : W := mkw 0x8080176dd42493dc 0x101002edba84927b 0x00003ffff00001f8 0x200007fffe00003f

def z676 : W := mkw 0x2000000002120000 0x0400000000424000 0xa00000000fff8000 0x1400000001fff000

def z677 : W := mkw 0x37d23fc886b681b0 0x26fa47f910d6d036 0xfff33ffccfff81ff 0xfffe67ff99fff03f

def z678 : W := mkw 0x84803bbee02412d8 0x90900777dc04825b 0x00003ffff00001f8 0x200007fffe00003f

def z679 : W := mkw 0x000545400c61e180 0x0000a8a8018c3c30 0x804fcfc00c63f1c3 0xf009f9f8018c7e38

def z680 : W := mkw 0x8197172dcc6c77d8 0x1032e2e5b98d8efb 0xa3bf3f3fcc7c7fff 0xf477e7e7f98f8fff

def z681 : W := mkw 0x00000561542091c4 0x000000ac2a841238 0x00000000000001c0 0x0000000000000038

def z682 : W := mkw 0x0c2c281209004800 0x0185850241200900 0xfc3c3c3f0f807e07 0x7f878787e1f00fc0

def z683 : W := mkw 0x36c03fe156b691f4 0x26d807fc2ad6d23e 0xffc03fe3ffff81ff 0xbff807fc7ffff03f

def z684 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5ffcfcdf30000005 0x0bff9f9be6000000

def z685 : W := mkw 0x93d39388e06c2490 0x927a72711c0d8492 0x03c3c3c0f07c0000 0x807878781e0f8000

def z686 : W := mkw 0xb3d3132cc27e36d8 0x167a6265984fc6db 0xfff3333ccfffffff 0xfffe666799ffffff

def z687 : W := mkw 0x0ca83a9aa0000000 0x8195075354000000 0x5c3c3ffff0000007 0x6b8787fffe000000

def z688 : W := mkw 0x2080174006b681b0 0x241002e800d6d036 0xa38033000fff81fe 0xb470066001fff03f

def z689 : W := mkw 0x093a801aa0000000 0x8127500354000000 0x0030001c00000000 0x0006000380000000

def z690 : W := mkw 0x36c03a8002960030 0x26d807500052c006 0x7fc03fc0039c003f 0xaff807f800738007

def z691 : W := mkw 0x1e68a89220000000 0x83cd151244000000 0x5c00000000000000 0x0b80000000000000

def z692 : W := mkw 0x7ffebfffafb6dbf8 0xafffd7fff5f6db7f 0xffffffffffffffff 0xffffffffffffffff

def z693 : W := mkw 0xc4803f3fc4a413f8 0x189007e7f894827f 0x00003f3fc00001f8 0x200007e7f800003f

def z694 : W := mkw 0x0001400000412000 0x0000280000082400 0x0043c00000638000 0x80087800000c7000

def z695 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0x0033333cc0007ff8 0x6006666798000fff

def z696 : W := mkw 0x9ffbbb9ae06c2490 0x93ff77735c0d8492 0x5ffffffff07c0007 0xebfffffffe0f8000

def z697 : W := mkw 0x493e803fa9005a48 0x8927d007f5200b49 0x003fc03ff0007e00 0x4007f807fe000fc0

def z698 : W := mkw 0x0000054004208180 0x000000a800841030 0x00000fc0000001c0 0x200001f800000038

def z699 : W := mkw 0x13d29288a0000000 0x827a525114000000 0x03cfcfe3f0000003 0xe079f9fc7e000000

def z700 : W := mkw 0x8081132cc06c36d8 0x10102265980d86db 0xa000333cc07c7ff8 0x34000667980f8fff

def z701 : W := mkw 0x0400289220000000 0x8080051244000000 0x00000cc330000000 0x0000019866000000

def z702 : W := mkw 0x85933f2cc4ec37f8 0x10b267e5989d86ff 0xffb33f3ccffc7fff 0xfff667e799ff8fff

def z703 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5ffff01c00000007 0xcbfffe0380000000

def z704 : W := mkw 0x24803fc006b681b0 0x249007f800d6d036 0xa0003fc00fff81f8 0x340007f801fff03f

def z705 : W := mkw 0x0112000000000000 0x0022400000000000 0x03b3000000000006 0xc076600000000000

def z706 : W := mkw 0x000404210c005140 0x0000808421800a28 0x804fcfe3fc0071c3 0xf009f9fc7f800e38

def z707 : W := mkw 0x0dba3a1a80000000 0x01b7474350000000 0x5ffffffff0000007 0xebfffffffe000000

def z708 : W := mkw 0x3b7b8000025a2400 0x076f7000004b4480 0xffffc0000ffffe07 0xdffff80001ffffc0

def z709 : W := mkw 0xbaecd32ccb375ad8 0x575d9a659966eb5b 0x5c4cf33ccf8381f9 0x2b899e6799f0703f

def z710 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xff8033000fff81fe 0xbff0066001fff03f

def z711 : W := mkw 0x8193132dd06c36dc 0x10326265ba0d86db 0xa3b3333ff07c7ffe 0xf4766667fe0f8fff

def z712 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xfffff03c0ffffe07 0xfffffe0781ffffc0

def z713 : W := mkw 0x0dbfffc00dededb0 0x61b7fff801bdbdb6 0x003fffc000007ff8 0x6007fff800000fff

def z714 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc7ffc3f0f807fff 0xff8fff87e1f00fff

def z715 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0xa04fffe3fc63f1ff 0xf409fffc7f8c7e3f

def z716 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc3c3c1f0f807ffd 0x1f878783e1f00fff

def z717 : W := mkw 0x17d23a8880000000 0x02fa475110000000 0x5ffffffff0000007 0xebfffffffe000000

def z718 : W := mkw 0x8192122c800c1658 0x10324245900182cb 0xa3b0301c001c7ffc 0x1476060380038fff

def z719 : W := mkw 0x600545655ff7fbfc 0x2c00a8acabfeff7f 0xa00000000ffffff8 0x1400000001ffffff

def z720 : W := mkw 0x493fc02509497e48 0x4927f804a1292fc9 0x003fc00000007e00 0x4007f80000000fc0

def z721 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0xffffffffff800007 0xfffffffffff00000

def z722 : W := mkw 0x4c29695651e1aaac 0x09852d2aca3c3555 0x7c73f3dcf3e38e3c 0x8f8e7e7b9e7c71c7

def z723 : W := mkw 0x400545655d61fbcc 0x0800a8acabac3f79 0x804fcfe3fc63ffc3 0xf009f9fc7f8c7ff8

def z724 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffc03fe3ffff81ff 0xbff807fc7ffff03f

def z725 : W := mkw 0x3240054006b681b0 0x264800a800d6d036 0xffc00fc00fff81ff 0xbff801f801fff03f

def z726 : W := mkw 0x0828001200000000 0x0105000240000000 0x007fcffff0000003 0xe00ff9fffe000000

def z727 : W := mkw 0x8193536cd06db6dc 0x10326a6d9a0db6db 0xa3b3333cc07ffffe 0xf4766667980fffff

def z728 : W := mkw 0x8192122c800c1658 0x10324245900182cb 0xa3b3333cc01c7ffe 0xf476666798038fff

def z729 : W := mkw 0x13d29288a0000000 0x827a525114000000 0x03fffffff0000007 0xe07ffffffe000000

def z730 : W := mkw 0x24857a9aab5b6c00 0xc490af53556b6d80 0xa0003ffffffffe00 0x340007ffffffffc0

def z731 : W := mkw 0x800545655c65f3dc 0x1000a8acab8cbe7b 0x804fcfe3fc63f1fb 0xf009f9fc7f8c7e3f

def z732 : W := mkw 0x3ffaba9aa2920020 0xa7ff575354524004 0x5fb0301c03800004 0x0bf6060380700000

def z733 : W := mkw 0x000545655c61f3cc 0x0000a8acab8c3e79 0x804ffffffc63f1fb 0xf009ffffff8c7e3f

def z734 : W := mkw 0x000545655c61f3cc 0x0000a8acab8c3e79 0xa00000000c63fff8 0x14000000018c7fff

def z735 : W := mkw 0xc00545655dedfffc 0x1800a8acabbdbfff 0xa04fcfe3fffffffb 0xf409f9fc7fffffff

def z736 : W := mkw 0x000444611c01d144 0x0000888c23803a28 0x804fcfe3fc03f1c3 0xf009f9fc7f807e38

def z737 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffb300000ffffe06 0xdff6600001ffffc0

def z738 : W := mkw 0x1ffffffbfc61f1c4 0x83ffffff7f8c3e38 0xdfb0301c0c63f1c4 0x1bf60603818c7e38

def z739 : W := mkw 0x36c57aa15ad77074 0x26d8af542b5aee0e 0x7f8ff023f39c703c 0x4ff1fe047e738e07

def z740 : W := mkw 0xb3d39308c27e2490 0x567a7261184fc492 0x03830300c07c0000 0x80706060180f8000

def z741 : W := mkw 0x0c2c2c120d804920 0x0185858241b00924 0xfc3c3c3f0f807fff 0x7f878787e1f00fff

def z742 : W := mkw 0x000545415c61e184 0x0000a8a82b8c3c30 0x804fcfc3fc63f003 0xd009f9f87f8c7e00

def z743 : W := mkw 0x7e6cec932f934920 0xcfcd9d9265f26924 0x5c4cccc33f838001 0x0b89999867f07000

def z744 : W := mkw 0x400545655de1fbec 0x0800a8acabbc3f7d 0xa07fffffffe3ffff 0xf40ffffffffc7fff

def z745 : W := mkw 0x893fc02dd9497e4c 0x5127f805bb292fc9 0x003fc03ff0007e00 0x4007f807fe000fc0

def z746 : W := mkw 0x7aec13f70b36dad8 0x2f5d827ee166db5b 0x03fc03ff007ffe00 0xc07f807fe00fffc0

def z747 : W := mkw 0x7753ec3706db3768 0x4eea7d86e0db66ed 0x03c3fc3f007f81f8 0xa0787f87e00ff03f

def z748 : W := mkw 0x3b7fc01aab5b6c00 0xc76ff803556b6d80 0xffffc01c0ffffe07 0xdffff80381ffffc0

def z749 : W := mkw 0x4c2c283609805a68 0x09858506c1300b4d 0xfc3c303c0f807fff 0x7f87860781f00fff

def z750 : W := mkw 0x8196564d9c0dc71c 0x1032cac9b381b8e3 0x23fcfcdf3c1f8e3d 0x047f9f9be783f1c7

def z751 : W := mkw 0x3b7fc0011b5b6c04 0x476ff800236b6d80 0xffffc0033ffffe07 0xdffff80067ffffc0

def z752 : W := mkw 0x3b7e80000b124800 0x076fd00001624900 0xffffc0000ffffe07 0xdffff80001ffffc0

def z753 : W := mkw 0x7e6cecd30f93c920 0x6fcd9d9a61f27924 0x5c4cccc30f838001 0x0b89999861f07000

def z754 : W := mkw 0x01931324006c36d8 0x00326264800d86db 0xa3b3333c007c7ffe 0xf4766667800f8fff

def z755 : W := mkw 0x4c28283601801a68 0x09850506c030034d 0xfc3c3c3f03807fff 0x7f878787e0700fff

def z756 : W := mkw 0x1ffaba9aa1080c00 0xc3ff575354210180 0x5ffffffff0000e07 0xebfffffffe0001c0

def z757 : W := mkw 0x000545615d69fdc4 0x4000a8ac2bad3fb8 0x804fcfe3fc63ffc3 0xf009f9fc7f8c7ff8

def z758 : W := mkw 0x4c2c2cb72d805b68 0x89858596e5b00b6d 0xfc3c3cff3f807fff 0x7f87879fe7f00fff

def z759 : W := mkw 0x000444411c01c104 0x0000888823803820 0x004fcfc3fc038001 0x8009f9f87f807000

def z760 : W := mkw 0x0000002400001248 0x0000000480000249 0xfc30303c0f807fff 0x7f86060781f00fff

def z761 : W := mkw 0x4c2c6c371d815b6c 0x09858d86e3b02b6d 0xfc3cfc3f3f807fff 0x7f879f87e7f00fff

def z762 : W := mkw 0x36c03fdaa6b681b0 0xa6d807fb54d6d036 0xffcfffffffff81ff 0xfff9fffffffff03f

def z763 : W := mkw 0x8193532cd06d36dc 0x10326a659a0da6db 0xa3b3f33cf07c7ffe 0xf4767e679e0f8fff

def z764 : W := mkw 0x3ffaba9aa2160010 0xa7ff57535442c002 0x5ffffffff01c0007 0xebfffffffe038000

def z765 : W := mkw 0x000105604460b1c0 0x000020ac088c1638 0x804fcfe3fc63f1c3 0xf009f9fc7f8c7e38

def z766 : W := mkw 0x0005402158417044 0x0000a8042b082e08 0x804fcfe3fc63f003 0xf009f9fc7f8c7e00

def z767 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xfff3c0000ffffe04 0x9ffe780001ffffc0

def z768 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b0333cc07c7ffc 0x34760667980f8fff

def z769 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xfff000000ffffe07 0x9ffe000001ffffc0

def z770 : W := mkw 0x1ffaba9aa0800020 0x83ff575354100004 0x7ffffffff380003f 0xeffffffffe700007

def z771 : W := mkw 0x3b7fc0802b5b6c00 0xc76ff810056b6d80 0xffffc0c03ffffe07 0xdffff81807ffffc0

def z772 : W := mkw 0x9e69a9b6606c36d8 0x93cd3536cc0d86db 0xfc4cccc3307c7ff9 0x1f899998660f8fff

def z773 : W := mkw 0x093fc02409497e48 0x4127f80481292fc9 0x003fc03c00007e00 0x4007f80780000fc0

def z774 : W := mkw 0x0c282c3604801368 0x01850586c090026d 0xfc3c3c3f0f807fff 0x7f878787e1f00fff

def z775 : W := mkw 0x0000002400001248 0x0000000480000249 0xa3b0303c007c7ffe 0xf4760607800f8fff

def z776 : W := mkw 0x3b7a8561573a9dc4 0x476f50ac2ae753b8 0x7fb00fe3f39c0fc4 0x2ff601fc7e7381f8

def z777 : W := mkw 0x3ffaba9aa21a0400 0xc7ff575354434080 0x5ffffffff01c0007 0xebfffffffe038000

def z778 : W := mkw 0x7e6cec531f93c924 0x4fcd9d8a63f27924 0x5c4cccc33f838001 0x0b89999867f07000

def z779 : W := mkw 0x4c2c2c771d80db6c 0x0985858ee3b01b6d 0xfc3c3cff3f807fff 0x7f87879fe7f00fff

def z780 : W := mkw 0x4c2c283709805a68 0x09858506e1300b4d 0xfc3c303f03807ffe 0x7f878607e0700fff

def z781 : W := mkw 0x36c03fd226b681b0 0xa6d807fa44d6d036 0xffc03fc33fff81ff 0xbff807f867fff03f

def z782 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b3303cc07c7ffc 0x54766607980f8fff

def z783 : W := mkw 0x400545615de1f9e4 0x0800a8ac2bbc3f3c 0x804fcfe3ffe3f1c3 0xf009f9fc7ffc7e38

def z784 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc3c301c0f807fff 0x5f87860381f00fff

def z785 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xffb3333ccffc7fff 0xfff6666799ff8fff

def z786 : W := mkw 0x8192132cc02c16d8 0x10324265980582db 0xa3b0333cc01c7ffe 0x7476066798038fff

def z787 : W := mkw 0x8113002cc0483648 0x10226005980906c9 0xa3b3303cc07c7ffe 0xf4766607980f8fff

def z788 : W := mkw 0xb6c03fc8c6b681b0 0x36d807f918d6d036 0xffc03fc0cfff81ff 0xbff807f819fff03f

def z789 : W := mkw 0x1ee8ba9aa0000000 0x83dd175354000000 0x5c4ffffff0000003 0xeb89fffffe000000

def z790 : W := mkw 0x000145405461a184 0x000028a80a8c3430 0x804fcfe3fc6381c3 0xf009f9fc7f8c7038

def z791 : W := mkw 0x482c04250d805b68 0x09058084a1b00b6d 0xfc3c303c0f807fff 0x7f87860781f00fff

def z792 : W := mkw 0xa00545655f7fffdc 0x5400a8acabeffffb 0xa00000000ffffff8 0x1400000001ffffff

def z793 : W := mkw 0x84803fe444a493f8 0x309007fc8894927f 0x00003fc0000001f8 0x200007f80000003f

def z794 : W := mkw 0x3240000002120000 0x0648000000424000 0xffc030000fff81ff 0xbff8060001fff03f

def z795 : W := mkw 0x293a855aa6b681b0 0xa52750ab54d6d036 0xa03fc03fffff81f8 0x5407f807fffff03f

def z796 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b33ffff07c7ffe 0xf47667fffe0f8fff

def z797 : W := mkw 0x093f400009496c00 0x0127e80001292d80 0xffffc0000ffffe07 0xdffff80001ffffc0

def z798 : W := mkw 0x324540000b5b6c00 0x4648a800016b6d80 0xff8000000ffffe04 0x1ff0000001ffffc0

def z799 : W := mkw 0x3ffaba9aa2120000 0x87ff575354424000 0x7ffffffff39c0007 0xeffffffffe738000

def z800 : W := mkw 0x0400282400801268 0x008005048010024d 0xfc30303c03807ffe 0x7f86060780700fff

def z801 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b3331cc07c7ffc 0x94766663980f8fff

def z802 : W := mkw 0xc00545655dedfffc 0x1800a8acabbdbfff 0xa00000000ffffff8 0x1400000001ffffff

def z803 : W := mkw 0x3b7f00000b5a6c00 0x076fe000016b4d80 0xffff00000ffffe07 0xdfffe00001ffffc0

def z804 : W := mkw 0x3b7fc01aab5b6c00 0xc76ff803556b6d80 0xffffcffffffffe07 0xfffff9ffffffffc0

def z805 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x004fcfe3fc6381c1 0xa009f9fc7f8c7038

def z806 : W := mkw 0x7e6cacd32f92c920 0xafcd959a65f25924 0x5c4cccc33f838001 0x0b89999867f07000

def z807 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xfff03fc00fffffff 0xfffe07f801ffffff

def z808 : W := mkw 0x800545655c65f3dc 0x1000a8acab8cbe7b 0x800000000c63f1f8 0x10000000018c7e3f

def z809 : W := mkw 0x84803fedd4a493fc 0x309007fdba94927f 0x00003ffff00001f8 0x200007fffe00003f

def z810 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffcfc0000ffffe01 0x9ff9f80001ffffc0

def z811 : W := mkw 0x44803ff754a493fc 0x289007feea94927f 0x00003ffff00001f8 0x200007fffe00003f

def z812 : W := mkw 0x0112002400081648 0x00224004800102c9 0xa3b0303c001c7ffe 0x7476060780038fff

def z813 : W := mkw 0x0000000000000000 0x0000000000000000 0x804fcfe3fc638003 0xf009f9fc7f8c7000

def z814 : W := mkw 0x0d3aa81aa0000000 0x81a7550354000000 0x5c7ffffff0000007 0xeb8ffffffe000000

def z815 : W := mkw 0x8080132cc02412d8 0x101002659804825b 0xa3b0333cc07c7ffe 0xf4760667980f8fff

def z816 : W := mkw 0xb7532cecc6dab768 0x36ea659d98db56ed 0x5c730cfccf83fe01 0x4b8e619f99f07fc0

def z817 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffbfc0000ffffe04 0x5ff7f80001ffffc0

def z818 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xff803c000fff81ff 0x3ff0078001fff03f

def z819 : W := mkw 0x4c2c6c771d81db6c 0x09858d8ee3b03b6d 0xfc7fffffff83ffff 0xff8ffffffff07fff

def z820 : W := mkw 0x0400281200000000 0x0080050240000000 0x004ffffff0000003 0xe009fffffe000000

def z821 : W := mkw 0xcdbf3f1bcdec6db0 0x19b7e7e379bd8db6 0x5f8f0f03cffc0001 0x8bf1e1e079ff8000

def z822 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffcfffc00fff81ff 0xfff9fff801fff03f

def z823 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffbc00000ffffe07 0x5ff7800001ffffc0

def z824 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xfff03ffc0fff81ff 0xfffe07ff81fff03f

def z825 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x004fcfe3fc63f001 0xc009f9fc7f8c7e00

def z826 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0xa07fcfe3fc63ffc7 0xf40ff9fc7f8c7ff8

def z827 : W := mkw 0x36c03e8006960130 0x26d807d000d2c026 0xffc03c000fff81ff 0xbff8078001fff03f

def z828 : W := mkw 0x53d696adad805b68 0x8a7ad2d5b5b00b6d 0xa3c3c3c0ff807ff8 0x947878781ff00fff

def z829 : W := mkw 0x0000000000000000 0x0000000000000000 0x007ffffff0000007 0xe00ffffffe000000

def z830 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0x23b3333cc01c7ffc 0x6476666798038fff

def z831 : W := mkw 0x000145615461b1c4 0x000028ac2a8c3638 0x004fcfe3f06381c3 0xe009f9fc7e0c7038

def z832 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc303c3f0f807ffc 0x3f860787e1f00fff

def z833 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b0303c007c7ffe 0x74760607800f8fff

def z834 : W := mkw 0x36402d4006b681b0 0x26c805a800d6d036 0xffc03c000fff81ff 0xbff8078001fff03f

def z835 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffffc023fffffe07 0xdffff8047fffffc0

def z836 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3f3333ccc7fffff 0xf47e6667998fffff

def z837 : W := mkw 0x3ffaba9aa3120800 0xc7ff575354624100 0x5ffffffff3800007 0xebfffffffe700000

def z838 : W := mkw 0x000545655c61f3cc 0x0000a8acab8c3e79 0x807fcffffc63ffc3 0xf00ff9ffff8c7ff8

def z839 : W := mkw 0x7e6c2c930f924920 0x2fcd859261f24924 0x5c0c0c030f800001 0x0b81818061f00000

def z840 : W := mkw 0x3ffaba9aa2120000 0x87ff575354424000 0x5fffffffff838007 0xebfffffffff07000

def z841 : W := mkw 0x4c28283601801a68 0x09850506c030034d 0xfc30301c03807ffc 0x1f86060380700fff

def z842 : W := mkw 0x000545415c61e184 0x0000a8a82b8c3c30 0x804fcfc3fc6381c3 0xb009f9f87f8c7038

def z843 : W := mkw 0x0dbaba9aa0000000 0x81b7575354000000 0x007ffffff0000003 0xe00ffffffe000000

def z844 : W := mkw 0x32c0174006b681b0 0x265802e800d6d036 0xffc033000fff81ff 0xbff8066001fff03f

def z845 : W := mkw 0x3ffaba9aa39e0c30 0xe7ff57535473c186 0x7ffffffff39c0e3f 0xeffffffffe7381c7

def z846 : W := mkw 0x76c03fd306b681b0 0x2ed807fa60d6d036 0xffc03fc30fff81ff 0xbff807f861fff03f

def z847 : W := mkw 0x3b7fc0005b5b6c04 0x476ff8000b6b6d80 0xffffc000fffffe07 0xdffff8001fffffc0

def z848 : W := mkw 0x7e6c2c130f924920 0x0fcd858261f24924 0x5c4c0c030f838001 0x0b89818061f07000

def z849 : W := mkw 0x8193536cd06db6dc 0x10326a6d9a0db6db 0xa3fffffff07fffff 0xf47ffffffe0fffff

def z850 : W := mkw 0x4c2cac372d805b68 0x89859586e5b00b6d 0xfc3cfc3f3f807fff 0x7f879f87e7f00fff

def z851 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b0331c007c7ffe 0xb4760663800f8fff

def z852 : W := mkw 0x4c2c2c375d805b6c 0x09858586ebb00b6d 0xfc3c3c3fff807fff 0x7f878787fff00fff

def z853 : W := mkw 0x7ffaba9ea39a0e28 0xcfff5753d47341c5 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z854 : W := mkw 0x000541405861e084 0x0000a8280b0c3c10 0x804fcfe3fc63f003 0xf009f9fc7f8c7e00

def z855 : W := mkw 0x32c0174006368190 0x065802e800c6d032 0xffc03fc00fff81ff 0xbff807f801fff03f

def z856 : W := mkw 0x000545615c65f1d4 0x0000a8ac2b8cbe3a 0xa04fcfe3fc7ff1fb 0xf409f9fc7f8ffe3f

def z857 : W := mkw 0x000545615d61f9c4 0x0000a8ac2bac3f38 0xa04fcfe3ffe3ffc3 0xf409f9fc7ffc7ff8

def z858 : W := mkw 0x400545655ce1f3ec 0x0800a8acab9c3e7d 0x800000000c63f1f8 0x10000000018c7e3f

def z859 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffc03cc00fff81fd 0x1ff8079801fff03f

def z860 : W := mkw 0x8193532cc06d36d8 0x10326a65980da6db 0xa3f3f33cc07ffffe 0xf47e7e67980fffff

def z861 : W := mkw 0x36402dc006b681b0 0x26c805b800d6d036 0xffc00cc00fff81ff 0x9ff8019801fff03f

def z862 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3b3301c007c7ffe 0xd4766603800f8fff

def z863 : W := mkw 0x1ee83a9200000000 0x03dd075240000000 0x5ffffffff0000007 0xebfffffffe000000

def z864 : W := mkw 0x493fc03759497e4c 0x4927f806eb292fc9 0x003fc03ff0007e00 0x4007f807fe000fc0

def z865 : W := mkw 0x5ffaba9aa1800820 0x8bff575354300104 0x5ffffffff3800007 0xebfffffffe700000

def z866 : W := mkw 0x0192132c802412d8 0x003242659004825b 0xa3b3333cc07c7ffe 0xf4766667980f8fff

def z867 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0xa3cfcfe3fc7ff1c7 0xf479f9fc7f8ffe38

def z868 : W := mkw 0x000544210c417140 0x0000a88421882e28 0x804fcfe3fc63f1c3 0xf009f9fc7f8c7e38

def z869 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffffcc230ffffe07 0xfffff98461ffffc0

def z870 : W := mkw 0x3b7e80000b1a4c00 0x476fd00001634980 0xfffc00000ffffe07 0xdfff800001ffffc0

def z871 : W := mkw 0x893fc03ee9497e48 0xd127f807dd292fc9 0x003fc03ff0007e00 0x4007f807fe000fc0

def z872 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0x5fffc0000ffffe01 0xcbfff80001ffffc0

def z873 : W := mkw 0x32c017c006b681b0 0x265802f800d6d036 0xffc003c00fff81ff 0x9ff8007801fff03f

def z874 : W := mkw 0x04803fe404a493f8 0x209007fc8094927f 0x00003ffc000001f8 0x200007ff8000003f

def z875 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0x03b3333cc07c7ff8 0xe0766667980f8fff

def z876 : W := mkw 0x8193d32cc06d36d8 0x50327a65980da6db 0xa3b3f33cc07c7ffe 0xf4767e67980f8fff

def z877 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xfffff0000fffffff 0xfffffe0001ffffff

def z878 : W := mkw 0x4c2c6c370d815b68 0x09858d86e1b02b6d 0xfc7cfc3f0f83ffff 0x7f8f9f87e1f07fff

def z879 : W := mkw 0x0c2c283609005a48 0x01858506c1200b49 0xfc3c3c3f0f807fff 0x7f878787e1f00fff

def z880 : W := mkw 0x3b7fc0088b5b6c00 0x476ff801116b6d80 0xffffc03ccffffe07 0xdffff80799ffffc0

def z881 : W := mkw 0xb3d393c8e27ea490 0xb67a72791c4fd492 0x03c3c3c0f07f8000 0x807878781e0ff000

def z882 : W := mkw 0x800545655c6df7dc 0x1000a8acab8dbefb 0xa07ffffffc7fffff 0xf40fffffff8fffff

def z883 : W := mkw 0x800545615c6df5d4 0x1000a8ac2b8dbeba 0x804fcfe3fc7ff1c3 0xf009f9fc7f8ffe38

def z884 : W := mkw 0x0000404010018004 0x0000080802003000 0x004fcfe3f0038003 0xe009f9fc7e007000

def z885 : W := mkw 0x093a801aa0000000 0x8127500354000000 0x003fcffff0000000 0x6007f9fffe000000

def z886 : W := mkw 0x3240054006b681b0 0x264800a800d6d036 0xff8000000fff81fc 0x1ff0000001fff03f

def z887 : W := mkw 0x0004400008014000 0x0000880001002800 0x004fcfe3fc038003 0xe009f9fc7f807000

def z888 : W := mkw 0x17d2ba9aa0000000 0x82fa575354000000 0x03cffffff0000003 0xe079fffffe000000

def z889 : W := mkw 0x000541615861f0c4 0x0000a82c2b0c3e18 0x004fcfe3f063f003 0xe009f9fc7e0c7e00

def z890 : W := mkw 0x36c0bfc026b681b0 0xa6d817f804d6d036 0xffc0ffc03fff81ff 0xbff81ff807fff03f

def z891 : W := mkw 0x000545615ce5f1f4 0x2000a8ac2b9cbe3e 0x804fcfe3fc63f1fb 0xf009f9fc7f8c7e3f

def z892 : W := mkw 0x1f7aa89aa0000000 0x83ef551354000000 0x5c7fcffff0000003 0xeb8ff9fffe000000

def z893 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fffcffff0000001 0xcbfff9fffe000000

def z894 : W := mkw 0x4c2c2c770d80db68 0x0985858ee1b01b6d 0xfc7c3cff0f83ffff 0x7f8f879fe1f07fff

def z895 : W := mkw 0xa00545655efff7fc 0x3400a8acabdffeff 0xa00000000ffffff8 0x1400000001ffffff

def z896 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0x5c3c3c3f0f807ff9 0x6b878787e1f00fff

def z897 : W := mkw 0x32c013c002368090 0x265802780046d012 0xffc033c00fff81ff 0xbff8067801fff03f

def z898 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffffc320cffffe07 0xfffff86419ffffc0

def z899 : W := mkw 0x000405610c20d1c0 0x000080ac21841a38 0x804fcfe3fc63f1c3 0xf009f9fc7f8c7e38

def z900 : W := mkw 0x36c03fc886b681b0 0x26d807f910d6d036 0xffc03ffccfff81ff 0xbff807ff99fff03f

def z901 : W := mkw 0x000544615c41f144 0x0000a88c2b883e28 0x004fcfe3fc03f003 0xe009f9fc7f807e00

def z902 : W := mkw 0xbffaba9ea31e0e18 0xd7ff5753d463c1c3 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z903 : W := mkw 0x36c03f0006b601b0 0x06d807e000d6c036 0xffc03f000fff81ff 0xbff807e001fff03f

def z904 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0xfffffffff00001ff 0xfffffffffe00003f

def z905 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x03fffffff0000000 0xe07ffffffe000000

def z906 : W := mkw 0x3240000002120000 0x0648000000424000 0xfff000000ffffe07 0xdffe000001ffffc0

def z907 : W := mkw 0x04803a9aa0000000 0x8090075354000000 0x000ffffff0000000 0x6001fffffe000000

def z908 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0xfc4fcfe3ffe3f1c7 0xff89f9fc7ffc7e38

def z909 : W := mkw 0x32410000025a2400 0x06482000004b4480 0xffc000000ffffe07 0x9ff8000001ffffc0

def z910 : W := mkw 0x4c2cec370d815b68 0x49859d86e1b02b6d 0xfc3cfc3f0f807fff 0x7f879f87e1f00fff

def z911 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0xdffffffffc638007 0xfbffffffff8c7000

def z912 : W := mkw 0x36c03fc116b681b4 0x26d807f822d6d036 0xffc03fc33fff81ff 0xbff807f867fff03f

def z913 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5c7ffffff0000001 0x6b8ffffffe000000

def z914 : W := mkw 0x84803ffee4a493f8 0xb09007ffdc94927f 0x00003ffff00001f8 0x200007fffe00003f

def z915 : W := mkw 0x3b7fc0120b5b6c00 0x476ff802416b6d80 0xffffc03f0ffffe07 0xdffff807e1ffffc0

def z916 : W := mkw 0x7b7fc0130b5b6c00 0x4f6ff802616b6d80 0xffffc0030ffffe07 0xdffff80061ffffc0

def z917 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fcffffff0000001 0xabf9fffffe000000

def z918 : W := mkw 0x000445411c21c184 0x000088a823843830 0x804fcfe3fc6381c3 0xf009f9fc7f8c7038

def z919 : W := mkw 0x0dbaba9aa0000000 0x81b7575354000000 0x03bffffff0000006 0xe077fffffe000000

def z920 : W := mkw 0x3357c0000b5b6c00 0x466af800016b6d80 0xffc3c0000ffffe07 0x9ff8780001ffffc0

def z921 : W := mkw 0x8193932ce06c36d8 0x903272659c0d86db 0xa3b3f33cf07c7ffe 0xf4767e679e0f8fff

def z922 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc7c3c3f0fe3ffff 0xff8f8787e1fc7fff

def z923 : W := mkw 0x44803fffa4a493f8 0xa89007fff494927f 0x00003ffff00001f8 0x200007fffe00003f

def z924 : W := mkw 0x81130124406c36d8 0x10226024880d86db 0xa3b3303c007c7ffe 0xf4766607800f8fff

def z925 : W := mkw 0x36402cc006928120 0x26c8059800d25024 0xffc03cc00fff81ff 0xbff8079801fff03f

def z926 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc3c303f0f807ffc 0x5f878607e1f00fff

def z927 : W := mkw 0x082c04250d005b48 0x01058084a1a00b69 0xfc3c3c3f0f807fff 0x7f878787e1f00fff

def z928 : W := mkw 0xb3d3d388e27f2490 0xd67a7a711c4fe492 0x03c3c3c0f07f8000 0x807878781e0ff000

def z929 : W := mkw 0x0000014000208080 0x0000002800041010 0x004fcfe3f0638003 0xe009f9fc7e0c7000

def z930 : W := mkw 0x1ffaba9aa0040010 0x83ff575354008002 0x7ffffffff01c003f 0xeffffffffe038007

def z931 : W := mkw 0x1ffaba9aa1000800 0x83ff575354200100 0x7ffffffff3800e07 0xeffffffffe7001c0

def z932 : W := mkw 0x482c003709005a48 0x09058006e1200b49 0xfc3c303f0f807fff 0x7f878607e1f00fff

def z933 : W := mkw 0x0dbaba9aa0000000 0x81b7575354000000 0x5c3ffffff0000007 0x6b87fffffe000000

def z934 : W := mkw 0x36c03fdaa6b681b0 0xa6d807fb54d6d036 0xffc03fdc0fff81ff 0xbff807fb81fff03f

def z935 : W := mkw 0xb3d3d3c8c27fa490 0x767a7a79184ff492 0x03c3c3c0c07f8000 0x80787878180ff000

def z936 : W := mkw 0xc93fc03fc9497e48 0x5927f807f9292fc9 0x003fc03fc0007e00 0x4007f807f8000fc0

def z937 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0x7c3c3c3f03807ffc 0x6f878787e0700fff

def z938 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xfffcc0000ffffe05 0x1fff980001ffffc0

def z939 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3fff33cc07c7fff 0xf47ffe67980f8fff

def z940 : W := mkw 0x8192132c802c16d8 0x10324265900582db 0xa3b0333c007c7ffe 0xf4760667800f8fff

def z941 : W := mkw 0x1e68a89220000000 0x83cd151244000000 0x5c7ffffff0000007 0xeb8ffffffe000000

def z942 : W := mkw 0x0000044004008100 0x0000008800801020 0x004fcfe3fc038003 0xe009f9fc7f807000

def z943 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0xfffffffff0007e07 0xfffffffffe000fc0

def z944 : W := mkw 0x1ffaba9aa0840030 0xa3ff575354108006 0x5ffffffff000003f 0xebfffffffe000007

def z945 : W := mkw 0x9ffaba9aa00c0410 0x93ff575354018082 0x5ffffffff01c0007 0xebfffffffe038000

def z946 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0xfffffffff07c0007 0xfffffffffe0f8000

def z947 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffc030000fff81ff 0x9ff8060001fff03f

def z948 : W := mkw 0xb3d3d348d27fa494 0x567a7a691a4ff492 0x03c3c3c0f07f8000 0x807878781e0ff000

def z949 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffc33fe0cfff81ff 0xfff867fc19fff03f

def z950 : W := mkw 0x3a6d40000b536800 0x074da800016a6d00 0xffffc0000ffffe07 0xdffff80001ffffc0

def z951 : W := mkw 0x4c282c3605801b68 0x09850586c0b0036d 0xfc303c3c0f807fff 0x7f86078781f00fff

def z952 : W := mkw 0x7e6cac130f924920 0x4fcd958261f24924 0x5c0c0c030f800001 0x0b81818061f00000

def z953 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0x5fc03fc00fff81f9 0xabf807f801fff03f

def z954 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffc3ffc0ffff81ff 0xbff87ff81ffff03f

def z955 : W := mkw 0x44042c250d805b68 0x08808584a1b00b6d 0xfc303c3c0f807fff 0x7f86078781f00fff

def z956 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffffcfc00ffffe07 0xfffff9f801ffffc0

def z957 : W := mkw 0x000545415c61e184 0x0000a8a82b8c3c30 0x004fcfe3fc638003 0xe009f9fc7f8c7000

def z958 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x807ffffffc63f1c7 0xf00fffffff8c7e38

def z959 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x804fcfc3fc63f1c1 0x9009f9f87f8c7e38

def z960 : W := mkw 0x800545655c69f7cc 0x1000a8acab8d3ef9 0x804fcfe3fc63ffc3 0xf009f9fc7f8c7ff8

def z961 : W := mkw 0x44002c3704801368 0x08800586e090026d 0xfc303c3f0f807fff 0x7f860787e1f00fff

def z962 : W := mkw 0x400545655d61fbcc 0x0800a8acabac3f79 0x800000000c63ffc0 0x10000000018c7ff8

def z963 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc30303c0f807ffe 0x7f86060781f00fff

def z964 : W := mkw 0x3ffaba9aa2160010 0xa7ff57535442c002 0x5fb0301c001c0004 0x0bf6060380038000

def z965 : W := mkw 0x000545655c61f3cc 0x0000a8acab8c3e79 0xa04fcfe3fc63fffb 0xf409f9fc7f8c7fff

def z966 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffcc3fe30fff81ff 0xfff987fc61fff03f

def z967 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc3c3fffff807fff 0x7f8787fffff00fff

def z968 : W := mkw 0x4c282c3705801b68 0x09850586e0b0036d 0xfc303c3f03807ffe 0x7f860787e0700fff

def z969 : W := mkw 0x324540000b5b6c00 0x4648a800016b6d80 0xffcfc0000ffffe07 0xdff9f80001ffffc0

def z970 : W := mkw 0x8193136cd06cb6dc 0x1032626d9a0d96db 0xa3b333fcf07c7ffe 0xf476667f9e0f8fff

def z971 : W := mkw 0x33d3d3c8a27fa490 0xe67a7a79144ff492 0x03c3c3c0f07f8000 0x807878781e0ff000

def z972 : W := mkw 0xc4803fffc4a493f8 0x389007fff894927f 0x00003fffc00001f8 0x200007fff800003f

def z973 : W := mkw 0x4c2c2c160d804b28 0x09858582c1b00965 0xfc3c3c1c0f807fff 0x7f87878381f00fff

def z974 : W := mkw 0x3ffaba9aa2120000 0x87ff575354424000 0x7fb0301c039c0004 0x0ff6060380738000

def z975 : W := mkw 0x3ffaba9aa21a0400 0xc7ff575354434080 0x5fb0301c001c0004 0x0bf6060380038000

def z976 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc7cfcff3f807fff 0x7f8f9f9fe7f00fff

def z977 : W := mkw 0x36c03e8006920120 0x06d807d000d24024 0xffc03fc00fff81ff 0xbff807f801fff03f

def z978 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc3ffc3fff807fff 0x7f87ff87fff00fff

def z979 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3bff33ff07c7ffe 0xf477fe67fe0f8fff

def z980 : W := mkw 0x3ffaba9aa2960030 0xa7ff57535452c006 0xffffffffffff803f 0xfffffffffffff007

def z981 : W := mkw 0x1ffaba9aa0000000 0x83ff575354000000 0x5fbffffff0000004 0x6bf7fffffe000000

def z982 : W := mkw 0x0001400000412000 0x0000280000082400 0x004fcfe3f0638003 0xe009f9fc7e0c7000

def z983 : W := mkw 0x36402d4006b281a0 0x06c805a800d65034 0xffc03fc00fff81ff 0xbff807f801fff03f

def z984 : W := mkw 0xbffaba9ea29e0638 0xb7ff5753d453c0c7 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z985 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffffccc33ffffe07 0xdffff99867ffffc0

def z986 : W := mkw 0xc4803f7fd4a493fc 0x189007effa94927f 0x00003ffff00001f8 0x200007fffe00003f

def z987 : W := mkw 0x000545615ce1f1e4 0x0000a8ac2b9c3e3c 0xa04fcfe3ffe3f1fb 0xf409f9fc7ffc7e3f

def z988 : W := mkw 0x400545655ce1f3ec 0x0800a8acab9c3e7d 0x804fcfe3fc63f1fb 0xf009f9fc7f8c7e3f

def z989 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc7c3fff0f807fff 0xff8f87ffe1f00fff

def z990 : W := mkw 0x000544411c41e104 0x0000a88823883c20 0x804fcfe3fc63f003 0xf009f9fc7f8c7e00

def z991 : W := mkw 0x000545615c69f5c4 0x0000a8ac2b8d3eb8 0xa04fcfe3fc7fffc3 0xf409f9fc7f8ffff8

def z992 : W := mkw 0x0112000880000000 0x0022400110000000 0x007fcffff0000003 0xe00ff9fffe000000

def z993 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc3f3f3fcf807fff 0xff87e7e7f9f00fff

def z994 : W := mkw 0xb3d31388c27e2490 0x367a6271184fc492 0x03830300c07c0000 0x80706060180f8000

def z995 : W := mkw 0x1f7aa81200000000 0x03ef550240000000 0x5ffffffff0000007 0xebfffffffe000000

def z996 : W := mkw 0x0080120880000000 0x0010024110000000 0x004ffffff0000003 0xe009fffffe000000

def z997 : W := mkw 0x00811324406432d8 0x00102264880c865b 0xa3b3333cc07c7ffe 0xf4766667980f8fff

def z998 : W := mkw 0x0828002401001a48 0x0105000480200349 0xfc30303c03807ffe 0x7f86060780700fff

def z999 : W := mkw 0x0000001aa0000000 0x8000000354000000 0x004fcffff0000003 0xe009f9fffe000000

def z1000 : W := mkw 0x3e6cecd22f93c920 0xe7cd9d9a45f27924 0x5c4cccc33f838001 0x0b89999867f07000

def z1001 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xff803fc00fff81fc 0x3ff007f801fff03f

def z1002 : W := mkw 0x8193122cc04c3658 0x10326245980986cb 0xa3b3303cc01c7ffe 0x7476660798038fff

def z1003 : W := mkw 0x0193122c80483648 0x00326245900906c9 0xa3b3333cc07c7ffe 0xf4766667980f8fff

def z1004 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x004fcfe3fc03f1c1 0x6009f9fc7f807e38

def z1005 : W := mkw 0xb3d31308c27e2490 0x167a6261184fc492 0x03c30300c07f8000 0x80786060180ff000

def z1006 : W := mkw 0x3ffaba9aa2920020 0xa7ff575354524004 0x5ffffffff3800007 0xebfffffffe700000

def z1007 : W := mkw 0x600545655ffbffec 0x4c00a8acabff7ffd 0xa00000000ffffff8 0x1400000001ffffff

def z1008 : W := mkw 0x09ba921aa0000000 0x8137524354000000 0x03fffffff0000007 0xe07ffffffe000000

def z1009 : W := mkw 0x00000561542091c4 0x000000ac2a841238 0x804fcfe3fc6381c3 0xf009f9fc7f8c7038

def z1010 : W := mkw 0x893fc02449497e48 0x5127f80489292fc9 0x003fc00000007e00 0x4007f80000000fc0

def z1011 : W := mkw 0x3a6cc0000b134800 0x474d980001626900 0xfffcc0000ffffe07 0xdfff980001ffffc0

def z1012 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3bf3f3fc07c7fff 0xf477e7e7f80f8fff

def z1013 : W := mkw 0x3ffaba9aa31a0c00 0xc7ff575354634180 0xffffffffffff8e07 0xfffffffffffff1c0

def z1014 : W := mkw 0x36c03fc8a6b681b0 0xa6d807f914d6d036 0xffc03fc0ffff81ff 0xbff807f81ffff03f

def z1015 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3f33ffcc07c7fff 0xf47e67ff980f8fff

def z1016 : W := mkw 0x293f40000b5b6c00 0x4527e800016b6d80 0xffbf00000ffffe07 0xdff7e00001ffffc0

def z1017 : W := mkw 0x3b7fc0000b5b6c00 0x476ff800016b6d80 0xffffc3c0fffffe07 0xdffff8781fffffc0

def z1018 : W := mkw 0x3b7b8000035a2c00 0x476f7000006b4580 0xfff300000ffffe07 0xdffe600001ffffc0

def z1019 : W := mkw 0x7e6c6cd31f93c924 0x2fcd8d9a63f27924 0x5c4cccc33f838001 0x0b89999867f07000

def z1020 : W := mkw 0x800545655c69f7cc 0x1000a8acab8d3ef9 0x800000000c63ffc0 0x10000000018c7ff8

def z1021 : W := mkw 0x36c03fd206b681b0 0x26d807fa40d6d036 0xffc03fff0fff81ff 0xbff807ffe1fff03f

def z1022 : W := mkw 0x1ffaba9aa0080400 0x83ff575354010080 0x7ffffffff01c0e07 0xeffffffffe0381c0

def z1023 : W := mkw 0x36c03b8002b600b0 0x26d807700056c016 0xffc033000fff81ff 0xbff8066001fff03f

def z1024 : W := mkw 0x3ffaba9aa3120800 0xc7ff575354624100 0x5fb0301c03800004 0x0bf6060380700000

def z1025 : W := mkw 0x05923a9aa0000000 0x80b2475354000000 0x03fffffff0000007 0xe07ffffffe000000

def z1026 : W := mkw 0x4c2c6c771d81db6c 0x09858d8ee3b03b6d 0xfc3c3c3f0f83ffff 0x7f878787e1f07fff

def z1027 : W := mkw 0x000545400c61e180 0x0000a8a8018c3c30 0x804fcfe3fc63f1c3 0xf009f9fc7f8c7e38

def z1028 : W := mkw 0x0080122400041258 0x001002448000824b 0xa3b0303c001c7ffe 0x7476060780038fff

def z1029 : W := mkw 0x0ca83a9aa0000000 0x8195075354000000 0x5c7ffffff0000007 0xeb8ffffffe000000

def z1030 : W := mkw 0x8193130c806c2698 0x10326261900d84d3 0xa3b3331c007c7ffe 0xf4766663800f8fff

def z1031 : W := mkw 0x3240040006920120 0x0648008000d24024 0xffc000000fff81ff 0x9ff8000001fff03f

def z1032 : W := mkw 0x335740000a5b6400 0x066ae800014b6c80 0xffffc0000ffffe07 0xdffff80001ffffc0

def z1033 : W := mkw 0x3ffaba9aa39e0c30 0xe7ff57535473c186 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z1034 : W := mkw 0x7ffaba9ea3960a38 0xafff5753d472c147 0x7fb0301c039c0e3c 0x0ff60603807381c7

def z1035 : W := mkw 0x0c2c2c240d805b68 0x0185858481b00b6d 0xfc3c3c3c0f807fff 0x7f87878781f00fff

def z1036 : W := mkw 0x3b7fc008ab5b6c00 0xc76ff801156b6d80 0xffffc000fffffe07 0xdffff8001fffffc0

def z1037 : W := mkw 0x36c03b8002360090 0x06d807700046c012 0xffc03fc00fff81ff 0xbff807f801fff03f

def z1038 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffc033c00fff81fc 0x9ff8067801fff03f

def z1039 : W := mkw 0x01130124406836c8 0x00226024880d06d9 0xa3b3333cc07c7ffe 0xf4766667980f8fff

def z1040 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffc00fc00fff81f9 0x9ff801f801fff03f

def z1041 : W := mkw 0x819313ace06c36d8 0x903262759c0d86db 0xa3b333fcf07c7ffe 0xf476667f9e0f8fff

def z1042 : W := mkw 0x3a6d40000b5b6c00 0x474da800016b6d80 0xfffc00000ffffe07 0xdfff800001ffffc0

def z1043 : W := mkw 0x819313ecc06cb6d8 0x3032627d980d96db 0xa3b333fcc07c7ffe 0xf476667f980f8fff

def z1044 : W := mkw 0x36c03fc056b681b4 0x26d807f80ad6d036 0xffc03fc0ffff81ff 0xbff807f81ffff03f

def z1045 : W := mkw 0x493fc03fa9497e48 0xc927f807f5292fc9 0x003fc03ff0007e00 0x4007f807fe000fc0

def z1046 : W := mkw 0xbb7fc008cb5b6c00 0x576ff801196b6d80 0xffffc000cffffe07 0xdffff80019ffffc0

def z1047 : W := mkw 0x1b7a801aa0000000 0x836f500354000000 0x5fffcffff0000007 0xebfff9fffe000000

def z1048 : W := mkw 0x8193122c804c3658 0x10326245900986cb 0xa3b3303c007c7ffe 0xf4766607800f8fff

def z1049 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xfc303c1c0f807fff 0x3f86078381f00fff

def z1050 : W := mkw 0x4c2c2c370d805b68 0x09858586e1b00b6d 0xffbc3c3f0ffc7fff 0xfff78787e1ff8fff

def z1051 : W := mkw 0x44803fe504a493f8 0x289007fca094927f 0x00003fc0000001f8 0x200007f80000003f

def z1052 : W := mkw 0x8193136cc06cb6d8 0x1032626d980d96db 0xa3f333fcc07ffffe 0xf47e667f980fffff

def z1053 : W := mkw 0x04803f4004a481b0 0x009007e800949036 0xffc03fc00fff81ff 0xbff807f801fff03f

def z1054 : W := mkw 0x01931308806c2490 0x00326261100d8492 0xa3b3333cc07c7ffe 0xf4766667980f8fff

def z1055 : W := mkw 0x335740000b5b6c00 0x466ae800016b6d80 0xfff300000ffffe07 0xdffe600001ffffc0

def z1056 : W := mkw 0x3a6dc0000b5b6c00 0x474db800016b6d80 0xffccc0000ffffe07 0x9ff9980001ffffc0

def z1057 : W := mkw 0x3ffaba9aa2120000 0x87ff575354424000 0x5ffffffff07f8007 0xebfffffffe0ff000

def z1058 : W := mkw 0x000141605061b0c4 0x0000282c0a0c3618 0x804fcfe3f063f1c3 0xf009f9fc7e0c7e38

def z1059 : W := mkw 0x00054120486170c0 0x0000a824090c2e18 0x804fcfe3fc63f1c3 0xf009f9fc7f8c7e38

def z1060 : W := mkw 0x000545615c61f1c4 0x0000a8ac2b8c3e38 0x004fcfe3f063f1c0 0xe009f9fc7e0c7e38

def z1061 : W := mkw 0x36c03fc006b681b0 0x26d807f800d6d036 0xffccffc33fff81ff 0xbff99ff867fff03f

def z1062 : W := mkw 0x3b7fc0122b5b6c00 0xc76ff802456b6d80 0xffffc0033ffffe07 0xdffff80067ffffc0

def z1063 : W := mkw 0x16c03a9aa0000000 0x82d8075354000000 0x5fcffffff0000007 0xebf9fffffe000000

def z1064 : W := mkw 0x000445615c21d1c4 0x000088ac2b843a38 0x004fcfe3fc0381c3 0xe009f9fc7f807038

def z1065 : W := mkw 0x8193132cc06c36d8 0x10326265980d86db 0xa3f3f3fcf07c7ffe 0xf47e7e7f9e0f8fff

def z1066 : W := mkw 0x80811324406c36d8 0x10102264880d86db 0xa3b0333c007c7ffe 0xf4760667800f8fff

def z1067 : W := mkw 0x4c2c2cf70d80db68 0x2985859ee1b01b6d 0xfc3c3cff0f807fff 0x7f87879fe1f00fff

def z1068 : W := mkw 0x04042c250c805368 0x00808584a1900a6d 0xfc3c3c3f0f807fff 0x7f878787e1f00fff

def z1069 : W := mkw 0x1bfa929aa0000000 0x837f525354000000 0x03ffcffff0000003 0xe07ff9fffe000000

def z1070 : W := mkw 0x1bfa920880000000 0x037f524110000000 0x5ffffffff0000007 0xebfffffffe000000

def z1071 : W := mkw 0x324400000b124800 0x0648800001624900 0xffc000000ffffe07 0x9ff8000001ffffc0

def z1072 : W := mkw 0x000141405061a084 0x000028280a0c3410 0x004fcfc3f0638001 0x8009f9f87e0c7000

def z1073 : W := mkw 0xb3d353c8d27fa494 0x367a6a791a4ff492 0x03c3c3c0f07f8000 0x807878781e0ff000

def z1074 : W := mkw 0xc93f403fd9497e4c 0x1927e807fb292fc9 0x003fc03ff0007e00 0x4007f807fe000fc0

def z1075 : W := mkw 0x3353c000025b2400 0x466a7800004b6480 0xfff3c0000ffffe07 0xdffe780001ffffc0

def z1076 : W := mkw 0x24803f4006b681b0 0x249007e800d6d036 0xff803f000fff81ff 0xbff007e001fff03f

def z1077 : W := mkw 0x3240010002360090 0x064800200046c012 0xffc000000fff81ff 0x9ff8000001fff03f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z8]),(0,[z1,z7,z3,z4,z5,z6,z9])],[(0,[z10,z11,z7,z3,z4,z5,z6])],[],[(0,[z1,z7,z12,z3,z4,z5,z6]),(0,[z1,z13,z7,z3,z4,z5,z6]),(0,[z1,z7,z14,z4,z15,z5,z6]),(0,[z1,z7,z3,z4,z16,z5,z6]),(0,[z1,z7,z4,z5,z6,z17,z18])],[(1,[z1,z7,z19,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z20,z6])],[(0,[z1,z7,z3,z4,z5,z21,z6]),(0,[z1,z7,z3,z4,z22,z5,z6])],[(0,[z1,z7,z3,z4,z23,z5,z6]),(0,[z1,z24,z7,z3,z4,z25,z6]),(0,[z1,z26,z7,z27,z3,z5,z6]),(0,[z1,z7,z3,z28,z4,z5,z6]),(0,[z1,z7,z3,z29,z5,z30,z6])],[(0,[z1,z7,z14,z3,z31,z5,z6]),(0,[z1,z32,z7,z3,z4,z5,z33]),(0,[z1,z7,z3,z4,z5,z34,z6]),(0,[z1,z35,z7,z36,z4,z5,z6])]],
   [[(0,[z1,z37,z38,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z39,z5,z6])],[(0,[z1,z7,z40,z3,z4,z5,z6]),(1,[z41,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z42,z5,z6])],[(0,[z1,z7,z3,z4,z5,z5,z6]),(0,[z1,z7,z43,z3,z4,z5,z6]),(0,[z1,z44,z7,z3,z4,z5,z6]),(0,[z45,z1,z7,z36,z3,z4,z5]),(0,[z1,z7,z36,z3,z4,z46,z5]),(0,[z47,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z48,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z49,z5,z6]),(0,[z1,z7,z50,z3,z4,z5,z6]),(0,[z10,z7,z3,z4,z5,z6,z51]),(1,[z52,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z53,z5,z6]),(0,[z1,z54,z55,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z56,z57]),(0,[z1,z7,z4,z58,z5,z59,z6]),(1,[z1,z7,z3,z4,z5,z60]),(0,[z1,z7,z3,z4,z61,z5,z6])],[(0,[z1,z7,z3,z62,z4,z5,z6])],[(0,[z1,z7,z3,z4,z63,z5,z6]),(0,[z1,z7,z3,z4,z5,z64,z6]),(0,[z1,z7,z65,z3,z4,z5,z6]),(0,[z1,z7,z3,z29,z4,z5,z6])],[(0,[z1,z66,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z67]),(0,[z1,z7,z68,z3,z4,z5,z6]),(0,[z1,z35,z7,z3,z4,z46,z5])]],
   [[(0,[z69,z1,z7,z3,z4,z5,z6]),(0,[z1,z70,z7,z3,z4,z5,z71]),(0,[z1,z7,z3,z4,z15,z5,z6]),(0,[z1,z7,z27,z3,z4,z72,z6]),(0,[z1,z7,z3,z4,z5,z73,z6])],[(0,[z74,z1,z7,z3,z4,z5,z6]),(0,[z75,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z76,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z77])],[(0,[z69,z1,z78,z3,z4,z5,z6]),(0,[z79,z11,z7,z3,z4,z5,z6]),(0,[z45,z1,z7,z3,z4,z5,z80]),(1,[z1,z81,z4,z82,z5,z6]),(0,[z1,z7,z3,z4,z83,z5,z6]),(0,[z1,z7,z14,z4,z5,z84,z6]),(1,[z1,z7,z85,z3,z5,z6]),(0,[z1,z7,z3,z4,z86,z5,z6]),(0,[z1,z87,z7,z3,z4,z6,z18]),(0,[z88,z1,z7,z3,z4,z5,z6])],[(0,[z89,z7,z90,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z91,z6]),(0,[z1,z7,z3,z4,z92,z5,z6]),(0,[z1,z93,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z94,z6]),(0,[z1,z95,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z96,z6])],[(0,[z1,z7,z3,z4,z5,z97,z6]),(0,[z1,z98,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z99,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z100,z6])],[(0,[z0,z1,z37,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z101,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z102]),(0,[z1,z7,z3,z4,z5,z6,z103])]],
   [[(0,[z104,z1,z7,z3,z4,z5,z6]),(0,[z1,z105,z7,z3,z4,z5,z6]),(1,[z7,z3,z4,z106,z5,z6]),(0,[z1,z7,z107,z3,z4,z5,z6]),(0,[z1,z108,z7,z3,z31,z5,z6]),(1,[z1,z109,z3,z4,z5,z6]),(0,[z1,z24,z7,z14,z4,z5,z6])],[(0,[z1,z7,z3,z4,z110,z5,z6]),(0,[z89,z1,z7,z3,z4,z5,z6]),(0,[z111,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z112,z6]),(1,[z1,z7,z27,z3,z72,z6])],[(1,[z1,z24,z7,z4,z57,z6])],[(0,[z113,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z114,z6]),(0,[z1,z7,z3,z4,z5,z6,z115])],[(0,[z1,z7,z116,z3,z4,z5,z6])],[(0,[z1,z7,z117,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z118]),(0,[z1,z7,z3,z4,z119,z5,z6]),(0,[z1,z7,z3,z4,z5,z120,z6]),(0,[z1,z7,z3,z4,z5,z71,z6]),(0,[z1,z121,z7,z3,z4,z5,z6]),(0,[z122,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z27,z3,z4,z25,z6])],[(0,[z1,z7,z3,z4,z5,z123,z6]),(0,[z1,z7,z3,z4,z124,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z125]),(0,[z1,z126,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z127,z5,z6])],[(0,[z69,z1,z7,z128,z4,z5,z6]),(0,[z1,z129,z7,z3,z4,z5,z6]),(0,[z1,z35,z7,z4,z5,z6,z130])]],
   [[(0,[z1,z7,z3,z4,z114,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z131]),(0,[z1,z7,z3,z4,z132,z5,z6]),(0,[z1,z7,z3,z4,z5,z84,z6])],[(0,[z1,z133,z90,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z134,z5,z6]),(0,[z1,z7,z3,z4,z135,z5,z6]),(0,[z1,z7,z136,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z137,z5,z6]),(0,[z138,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z139,z6])],[(0,[z1,z7,z3,z140,z4,z5,z6]),(0,[z1,z141,z7,z3,z4,z5,z6])],[(0,[z1,z142,z7,z3,z4,z5,z6]),(0,[z143,z7,z3,z4,z5,z80,z6])],[(0,[z69,z10,z7,z3,z4,z5,z6]),(0,[z144,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z145,z6]),(0,[z1,z7,z3,z4,z5,z71,z51]),(0,[z1,z7,z3,z4,z5,z6,z146]),(0,[z1,z7,z14,z3,z5,z30,z6]),(0,[z1,z24,z7,z3,z4,z5,z6]),(0,[z147,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z59,z6]),(0,[z1,z7,z148,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z149,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z150]),(0,[z1,z151,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z152,z5,z6])],[(0,[z1,z7,z38,z90,z4,z5,z6]),(0,[z1,z7,z3,z4,z153,z5,z6]),(0,[z10,z7,z3,z4,z154,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z155]),(0,[z1,z7,z3,z5,z30,z6,z18])]],
   [[(1,[z1,z156,z3,z4,z5,z6]),(0,[z1,z157,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z158,z5,z6]),(0,[z1,z7,z159,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z160,z6]),(0,[z1,z7,z3,z4,z5,z161,z6]),(0,[z1,z70,z3,z4,z5,z6,z33]),(0,[z1,z7,z3,z4,z5,z162,z6])],[(0,[z89,z1,z7,z163,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z164,z6]),(0,[z1,z35,z7,z3,z4,z5,z130]),(0,[z1,z7,z165,z3,z4,z5,z6])],[(0,[z1,z166,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z167,z4,z5,z6]),(0,[z1,z2,z168,z3,z4,z5,z6]),(0,[z1,z169,z7,z3,z4,z5,z6]),(0,[z1,z26,z7,z3,z4,z72,z6]),(0,[z1,z7,z3,z4,z5,z6,z170])],[(0,[z69,z7,z3,z171,z4,z5,z6]),(0,[z0,z1,z3,z4,z172,z5,z6]),(0,[z1,z7,z163,z4,z82,z5,z6])],[(0,[z173,z1,z7,z3,z4,z5,z6]),(0,[z1,z174,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z175,z6])],[(0,[z1,z7,z3,z4,z5,z176,z6]),(0,[z1,z7,z177,z3,z4,z5,z6]),(1,[z143,z7,z3,z4,z5,z80]),(0,[z1,z109,z14,z3,z4,z5,z6]),(0,[z45,z1,z7,z3,z4,z46,z6])],[(0,[z1,z7,z3,z4,z178,z5,z6]),(0,[z1,z32,z7,z3,z4,z5,z71])]],
   [[(0,[z69,z1,z7,z3,z179,z5,z6]),(0,[z69,z7,z3,z4,z5,z6,z51]),(0,[z1,z180,z7,z3,z4,z5,z6]),(0,[z1,z181,z12,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z182,z6])],[(0,[z1,z7,z7,z3,z4,z5,z6]),(0,[z1,z7,z183,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z184]),(0,[z1,z7,z3,z4,z5,z6,z185]),(0,[z52,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z186,z3,z4,z16,z6]),(0,[z1,z7,z3,z4,z5,z6,z187]),(0,[z1,z188,z7,z3,z4,z5,z6])],[(0,[z189,z7,z3,z4,z5,z190,z6]),(0,[z1,z7,z3,z4,z191,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z192])],[(0,[z1,z193,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z171,z4,z5,z6]),(0,[z194,z1,z7,z3,z4,z5,z6]),(0,[z1,z81,z7,z3,z4,z5,z6]),(0,[z1,z195,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z196,z5,z6]),(0,[z1,z24,z55,z7,z4,z5,z6])],[(0,[z1,z7,z3,z4,z197,z5,z6]),(0,[z1,z7,z3,z4,z5,z198,z6]),(0,[z7,z3,z4,z5,z190,z6,z51]),(0,[z199,z1,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z172,z200,z5,z6]),(0,[z1,z54,z7,z14,z4,z5,z6])],[],[(0,[z1,z201,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z202,z5,z6]),(0,[z1,z7,z203,z3,z4,z5,z6]),(0,[z45,z1,z7,z3,z4,z5,z25])],[(0,[z1,z7,z3,z4,z5,z6,z51]),(0,[z52,z7,z3,z4,z5,z71,z6]),(0,[z1,z204,z7,z3,z29,z5,z6]),(0,[z1,z7,z205,z3,z4,z5,z6])]],
   [[(0,[z206,z1,z7,z3,z4,z5,z6]),(0,[z1,z26,z7,z3,z4,z25,z6])],[(0,[z1,z7,z3,z4,z5,z6,z207]),(0,[z208,z1,z7,z3,z4,z5,z6]),(0,[z1,z24,z7,z3,z4,z16,z6]),(0,[z1,z7,z3,z209,z5,z57,z6])],[(0,[z210,z1,z7,z3,z4,z5,z6]),(0,[z211,z1,z7,z3,z4,z5,z6]),(0,[z1,z81,z7,z38,z4,z5,z6])],[(0,[z1,z212,z7,z3,z4,z5,z6]),(0,[z1,z213,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z214,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z215]),(0,[z1,z7,z3,z4,z5,z6,z216]),(0,[z1,z7,z3,z4,z217,z5,z6])],[(0,[z218,z1,z7,z3,z4,z5,z6]),(0,[z219,z1,z7,z3,z171,z5,z6]),(0,[z45,z1,z24,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z5,z6,z130]),(0,[z1,z7,z27,z3,z4,z5,z6]),(0,[z1,z220,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z221,z6]),(0,[z1,z7,z222,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z223,z6])],[(0,[z224,z1,z7,z3,z4,z5,z6]),(0,[z225,z1,z7,z3,z4,z5,z6])],[(0,[z69,z1,z3,z4,z5,z71,z6]),(0,[z189,z1,z7,z3,z4,z190,z6]),(0,[z1,z7,z3,z226,z4,z5,z6]),(0,[z1,z227,z7,z3,z4,z5,z6]),(0,[z1,z7,z228,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z200,z5,z6]),(0,[z1,z7,z3,z4,z229,z5,z6]),(0,[z1,z230,z7,z3,z4,z5,z6]),(1,[z1,z7,z205,z4,z5,z6])]],
   [[(1,[z1,z3,z4,z5,z231,z6]),(0,[z232,z1,z7,z3,z4,z5,z6])],[(0,[z69,z1,z7,z3,z4,z49,z6]),(0,[z1,z7,z3,z4,z5,z233,z6]),(0,[z1,z234,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z235,z6]),(0,[z236,z1,z7,z3,z4,z5,z6]),(0,[z1,z54,z7,z3,z4,z5,z6]),(0,[z1,z237,z7,z3,z4,z5,z6]),(0,[z1,z7,z186,z3,z4,z25,z6]),(0,[z1,z7,z36,z4,z5,z84,z6])],[(0,[z1,z7,z238,z3,z4,z5,z6]),(1,[z1,z7,z36,z4,z5,z84]),(1,[z1,z26,z7,z3,z59,z6]),(0,[z1,z7,z3,z4,z5,z60,z59])],[(1,[z1,z7,z3,z239,z5,z6]),(0,[z69,z1,z7,z3,z4,z221,z6]),(0,[z1,z240,z7,z3,z4,z5,z6]),(0,[z10,z1,z7,z3,z4,z190,z6]),(0,[z241,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z242,z6])],[(0,[z1,z7,z12,z14,z3,z5,z6])],[(0,[z1,z7,z3,z4,z243,z5,z6]),(0,[z1,z37,z7,z3,z244,z5,z6]),(0,[z1,z245,z7,z3,z4,z5,z6])],[(0,[z1,z7,z85,z3,z5,z6,z130])]],
   [[(0,[z1,z7,z3,z4,z5,z246,z6]),(0,[z247,z1,z7,z3,z171,z5,z6]),(0,[z1,z7,z3,z4,z5,z248,z6]),(0,[z7,z3,z4,z5,z71,z249,z6])],[(0,[z1,z7,z3,z128,z4,z5,z6]),(0,[z1,z7,z3,z4,z250,z5,z6]),(1,[z1,z7,z3,z4,z5,z56]),(0,[z1,z7,z3,z251,z4,z5,z6]),(0,[z1,z7,z27,z3,z72,z5,z6])],[(0,[z69,z143,z7,z3,z4,z5,z6]),(1,[z1,z133,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z252]),(1,[z1,z3,z4,z253,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z17])],[(0,[z1,z254,z7,z3,z4,z5,z6]),(0,[z1,z7,z255,z3,z4,z5,z6]),(0,[z1,z256,z7,z3,z4,z5,z6]),(0,[z1,z257,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z258,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z259]),(0,[z1,z7,z3,z4,z46,z5,z170])],[(0,[z69,z1,z7,z3,z4,z5,z260]),(0,[z69,z1,z2,z3,z4,z5,z6]),(0,[z261,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z262]),(0,[z1,z263,z7,z3,z4,z5,z6]),(0,[z41,z7,z3,z4,z31,z5,z6])],[(0,[z1,z7,z3,z4,z5,z264,z6]),(0,[z265,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z266]),(0,[z1,z267,z7,z3,z4,z5,z6])],[(0,[z69,z0,z7,z3,z4,z5,z6]),(0,[z69,z7,z90,z3,z4,z5,z6]),(0,[z1,z7,z268,z3,z4,z5,z6]),(0,[z1,z55,z7,z3,z4,z5,z6]),(0,[z1,z54,z7,z3,z72,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z269])],[(0,[z1,z7,z270,z3,z4,z5,z6]),(0,[z7,z3,z4,z154,z5,z190,z6]),(1,[z1,z271,z7,z3,z4,z5])]],
   [[(0,[z69,z247,z7,z3,z4,z5,z6]),(0,[z11,z7,z3,z171,z4,z5,z6]),(1,[z1,z87,z7,z3,z4,z6])],[(0,[z69,z1,z7,z3,z4,z5,z272]),(0,[z11,z7,z78,z3,z4,z5,z6]),(0,[z1,z7,z273,z3,z4,z5,z6])],[(0,[z79,z1,z7,z163,z4,z5,z6]),(0,[z274,z1,z7,z3,z4,z5,z6]),(0,[z275,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z276,z4,z5,z6]),(0,[z1,z277,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z278,z4,z5,z6]),(0,[z1,z35,z7,z14,z4,z5,z6]),(0,[z1,z279,z7,z3,z4,z6,z130])],[(0,[z280,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z209,z5,z6]),(0,[z1,z87,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z281,z5,z6])],[(0,[z282,z1,z7,z3,z4,z5,z6]),(0,[z79,z1,z7,z90,z4,z5,z6]),(0,[z1,z7,z90,z3,z4,z5,z6]),(0,[z283,z1,z7,z3,z4,z5,z6]),(0,[z1,z55,z7,z38,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z284,z6]),(0,[z1,z7,z3,z4,z5,z60,z6]),(0,[z1,z7,z3,z285,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z286])],[(0,[z1,z7,z3,z4,z239,z5,z6]),(0,[z1,z7,z287,z3,z4,z5,z6]),(0,[z1,z7,z288,z3,z4,z5,z6]),(0,[z1,z289,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z46,z5,z25])],[(0,[z290,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z291,z6]),(0,[z1,z7,z3,z4,z46,z5,z51]),(0,[z1,z26,z7,z3,z4,z5,z6]),(0,[z1,z7,z27,z3,z4,z59,z6])]],
   [[(0,[z1,z7,z3,z4,z292,z5,z6]),(0,[z293,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z294,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z31,z5,z6]),(0,[z1,z295,z7,z3,z4,z5,z6]),(0,[z219,z1,z7,z3,z296,z5,z6]),(1,[z1,z297,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z298])],[(0,[z1,z1,z7,z3,z4,z5,z6]),(0,[z69,z7,z3,z4,z5,z190,z6]),(1,[z1,z3,z4,z299,z5,z6]),(0,[z1,z7,z300,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z301,z5,z6])],[(0,[z143,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z302,z6]),(0,[z1,z7,z3,z4,z5,z6,z303]),(0,[z1,z54,z55,z7,z3,z5,z6])],[(0,[z0,z1,z3,z4,z82,z5,z6]),(0,[z304,z1,z7,z3,z4,z5,z6]),(1,[z1,z181,z12,z3,z5,z6]),(1,[z7,z3,z4,z5,z249,z6])],[(0,[z1,z305,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z306])],[(0,[z307,z1,z7,z3,z4,z5,z6]),(0,[z1,z181,z7,z3,z4,z5,z6]),(0,[z1,z204,z7,z3,z5,z6,z18])],[(0,[z1,z7,z3,z4,z5,z6,z308]),(0,[z1,z3,z4,z172,z5,z120,z6])]],
   [[(0,[z1,z7,z309,z3,z4,z5,z6]),(0,[z1,z310,z7,z3,z4,z5,z6]),(0,[z1,z70,z7,z3,z4,z5,z6]),(0,[z1,z7,z186,z3,z4,z5,z6]),(0,[z1,z35,z7,z3,z4,z5,z6]),(0,[z1,z7,z36,z3,z4,z5,z84])],[(0,[z1,z7,z3,z4,z5,z190,z6]),(0,[z1,z7,z3,z4,z311,z5,z6]),(0,[z312,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z313]),(0,[z1,z7,z3,z4,z5,z6,z314]),(0,[z315,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z316]),(0,[z1,z7,z3,z4,z5,z317,z6])],[(0,[z69,z1,z37,z3,z4,z5,z6]),(0,[z143,z1,z7,z3,z4,z5,z51]),(0,[z1,z7,z3,z209,z4,z5,z6]),(0,[z1,z318,z7,z3,z4,z5,z6]),(0,[z1,z7,z319,z3,z4,z5,z6])],[(0,[z219,z1,z7,z3,z4,z5,z6]),(0,[z1,z168,z3,z4,z172,z5,z6]),(0,[z1,z279,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z320])],[(0,[z247,z1,z7,z3,z296,z5,z6]),(0,[z1,z7,z3,z4,z321,z5,z6]),(0,[z1,z7,z3,z4,z154,z120,z6]),(0,[z1,z7,z3,z4,z322,z5,z6]),(0,[z143,z1,z7,z3,z4,z91,z6]),(0,[z1,z54,z7,z3,z15,z5,z6]),(0,[z1,z35,z7,z3,z4,z5,z84]),(0,[z1,z7,z323,z3,z4,z5,z6])],[(0,[z324,z1,z7,z3,z4,z5,z6]),(0,[z325,z1,z7,z3,z4,z5,z6])],[(0,[z326,z1,z7,z3,z4,z5,z6]),(0,[z1,z327,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z80,z33]),(0,[z1,z7,z36,z3,z4,z5,z130])],[(0,[z328,z1,z7,z3,z4,z5,z6]),(0,[z1,z37,z7,z3,z4,z5,z6]),(0,[z1,z70,z32,z3,z4,z5,z6])],[(0,[z1,z7,z329,z3,z4,z5,z6]),(0,[z1,z330,z7,z3,z4,z5,z6]),(0,[z1,z24,z7,z4,z5,z57,z6]),(0,[z1,z7,z3,z4,z5,z331,z6]),(0,[z1,z7,z3,z4,z25,z6,z170])],[(0,[z1,z7,z3,z4,z332,z5,z6]),(1,[z1,z7,z3,z4,z5,z145]),(0,[z333,z7,z3,z4,z82,z5,z6]),(0,[z1,z181,z108,z3,z4,z5,z6]),(0,[z334,z1,z7,z3,z4,z5,z6]),(0,[z1,z32,z3,z4,z5,z71,z6]),(0,[z1,z271,z7,z3,z4,z5,z59])],[(0,[z335,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z336,z6]),(0,[z1,z7,z337,z3,z4,z5,z6])],[(0,[z1,z7,z338,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z339,z6]),(0,[z1,z7,z3,z4,z340,z5,z6])],[(0,[z10,z189,z7,z3,z4,z5,z6]),(0,[z1,z181,z37,z3,z4,z5,z6]),(0,[z341,z1,z7,z3,z4,z5,z6]),(0,[z1,z35,z55,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z342]),(0,[z45,z1,z7,z3,z4,z5,z170])],[(0,[z1,z11,z7,z3,z4,z5,z6]),(0,[z343,z1,z7,z3,z4,z5,z6]),(0,[z1,z90,z3,z4,z149,z5,z6]),(1,[z189,z7,z3,z4,z190,z6]),(0,[z45,z1,z7,z3,z4,z154,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z344,z6]),(0,[z89,z1,z7,z90,z4,z5,z6]),(0,[z247,z1,z7,z3,z4,z5,z6]),(0,[z345,z143,z7,z3,z4,z5,z6]),(0,[z1,z37,z7,z38,z4,z5,z6]),(1,[z7,z3,z4,z346,z5,z6]),(0,[z1,z7,z14,z3,z4,z5,z6])],[(0,[z1,z7,z3,z179,z4,z5,z6]),(0,[z1,z347,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z82,z31,z5,z6]),(0,[z348,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z349,z6])],[(0,[z350,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z6]),(0,[z1,z7,z3,z4,z351,z5,z6]),(0,[z1,z26,z7,z3,z4,z59,z6]),(0,[z45,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z352])],[(1,[z1,z7,z116,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z353]),(0,[z10,z1,z7,z3,z4,z5,z118]),(0,[z1,z7,z3,z4,z5,z354,z6]),(1,[z1,z7,z3,z244,z5,z6]),(0,[z1,z7,z3,z4,z5,z355,z6]),(0,[z1,z7,z3,z4,z46,z25,z6])],[(0,[z1,z7,z3,z356,z4,z5,z6]),(0,[z1,z7,z3,z4,z357,z5,z6]),(0,[z1,z7,z3,z29,z4,z5,z30]),(0,[z1,z358,z7,z3,z4,z5,z6])],[(0,[z79,z7,z3,z163,z4,z5,z6]),(0,[z1,z7,z3,z4,z359,z5,z6]),(0,[z1,z7,z360,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z361,z5,z6]),(0,[z1,z7,z3,z4,z154,z25,z6]),(0,[z1,z7,z362,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z192,z130]),(0,[z1,z363,z7,z3,z4,z5,z6])],[(0,[z1,z181,z7,z364,z4,z5,z6]),(0,[z1,z365,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z366,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z367]),(0,[z1,z7,z3,z4,z5,z368,z6]),(0,[z1,z7,z369,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z370]),(0,[z345,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z371,z4,z5,z6]),(0,[z1,z372,z7,z3,z4,z5,z6]),(0,[z1,z7,z373,z3,z4,z5,z6]),(0,[z1,z168,z7,z3,z4,z172,z6])],[(0,[z1,z7,z3,z4,z5,z260,z6]),(0,[z1,z7,z374,z3,z4,z5,z6]),(0,[z45,z1,z7,z3,z4,z5,z51]),(0,[z1,z7,z3,z29,z4,z46,z5])],[(0,[z1,z7,z375,z3,z4,z5,z6])],[(0,[z45,z376,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z377,z6]),(1,[z1,z108,z3,z31,z5,z6]),(0,[z1,z7,z14,z3,z72,z5,z6]),(0,[z1,z378,z7,z3,z4,z5,z6])],[(0,[z11,z7,z3,z4,z5,z190,z6]),(0,[z1,z7,z3,z4,z379,z5,z6]),(0,[z1,z380,z7,z3,z4,z5,z6]),(0,[z1,z271,z7,z3,z4,z5,z6])],[(0,[z0,z1,z11,z3,z4,z5,z6]),(0,[z1,z381,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z382,z5,z6]),(0,[z1,z383,z7,z3,z4,z5,z6]),(0,[z1,z81,z7,z4,z82,z5,z6]),(0,[z1,z32,z7,z3,z4,z5,z6])]],
   [[(0,[z219,z7,z3,z171,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z384,z6]),(0,[z385,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z386,z3,z4,z5,z6]),(0,[z345,z1,z7,z3,z4,z5,z51]),(0,[z1,z7,z3,z387,z4,z5,z6]),(0,[z1,z7,z19,z3,z4,z5,z6]),(0,[z1,z108,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z388,z5,z6]),(0,[z1,z7,z3,z5,z6,z125,z130]),(0,[z1,z204,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z6,z389])],[(1,[z219,z7,z3,z171,z5,z6]),(0,[z1,z7,z3,z4,z190,z120,z6]),(0,[z1,z7,z3,z4,z5,z390,z6])],[(0,[z1,z7,z3,z4,z5,z391,z6]),(0,[z1,z392,z7,z3,z4,z5,z6]),(0,[z1,z393,z7,z3,z4,z5,z6]),(0,[z1,z24,z7,z186,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z394,z6]),(0,[z1,z395,z7,z3,z4,z5,z6]),(0,[z1,z7,z205,z4,z5,z6,z18]),(0,[z45,z157,z7,z3,z4,z5,z6])],[(0,[z0,z1,z78,z3,z4,z5,z6]),(0,[z396,z1,z7,z3,z4,z5,z6]),(0,[z1,z181,z7,z268,z4,z5,z6])],[(0,[z247,z11,z7,z3,z4,z5,z6]),(0,[z1,z397,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z398,z5,z6])],[],[(0,[z69,z1,z181,z3,z4,z5,z6]),(0,[z1,z7,z399,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z400,z6]),(0,[z1,z7,z3,z4,z5,z6,z401]),(0,[z1,z7,z3,z4,z58,z5,z6])],[(0,[z1,z168,z7,z3,z4,z120,z6]),(0,[z1,z7,z402,z3,z4,z5,z6])],[(0,[z403,z1,z7,z3,z4,z5,z6])],[(0,[z69,z1,z70,z3,z4,z5,z6]),(1,[z1,z3,z4,z149,z5,z6]),(0,[z1,z7,z3,z4,z5,z404,z6]),(0,[z1,z7,z3,z4,z405,z5,z6])],[(0,[z1,z406,z7,z3,z4,z5,z6]),(0,[z1,z7,z407,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z408]),(0,[z1,z204,z54,z7,z3,z5,z6])],[(0,[z1,z7,z409,z3,z4,z5,z6]),(0,[z410,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z411,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z412,z6])],[(0,[z1,z413,z7,z3,z4,z5,z6]),(0,[z1,z414,z7,z3,z4,z5,z6]),(0,[z415,z1,z7,z3,z4,z5,z6])],[(1,[z0,z11,z3,z4,z5,z6]),(0,[z1,z54,z26,z7,z3,z5,z6])]],
   [[(0,[z1,z7,z416,z3,z4,z5,z6]),(0,[z1,z417,z7,z3,z4,z5,z6]),(0,[z1,z54,z7,z12,z3,z5,z6]),(0,[z1,z55,z7,z14,z3,z5,z6]),(0,[z1,z418,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z419,z5,z6]),(0,[z1,z26,z7,z3,z5,z59,z6])],[(0,[z420,z1,z7,z3,z4,z5,z6]),(0,[z1,z421,z3,z4,z5,z190,z6])],[(0,[z1,z3,z4,z299,z5,z190,z6]),(0,[z1,z422,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z423,z6]),(0,[z1,z424,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z425,z5,z6]),(1,[z1,z32,z3,z4,z5,z71]),(0,[z1,z7,z3,z4,z46,z5,z6])],[(0,[z426,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z427,z5,z6]),(0,[z1,z428,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z190,z25,z6]),(0,[z1,z7,z3,z4,z5,z429,z6]),(0,[z1,z7,z3,z4,z430,z5,z6]),(0,[z431,z1,z7,z3,z4,z5,z6]),(0,[z1,z432,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z433])],[(0,[z1,z7,z3,z4,z5,z434,z6]),(0,[z1,z7,z14,z3,z15,z5,z6]),(0,[z1,z435,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z154,z5,z6]),(0,[z7,z3,z4,z5,z80,z6,z51]),(0,[z1,z7,z3,z4,z5,z436,z6]),(0,[z1,z437,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z172,z154,z6]),(0,[z1,z7,z438,z3,z4,z5,z6]),(0,[z1,z7,z3,z364,z4,z5,z6]),(0,[z439,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z440,z6])],[(0,[z11,z7,z3,z4,z5,z6,z51]),(1,[z79,z7,z163,z4,z5,z6]),(0,[z1,z7,z3,z4,z441,z5,z6]),(0,[z1,z7,z3,z4,z442,z5,z6]),(0,[z1,z7,z3,z4,z443,z5,z6]),(0,[z1,z444,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z445,z6]),(0,[z1,z7,z12,z3,z171,z5,z6]),(0,[z446,z1,z7,z3,z4,z5,z6]),(0,[z447,z1,z7,z3,z4,z5,z6]),(0,[z1,z448,z7,z3,z4,z5,z6])],[(0,[z1,z449,z7,z3,z4,z5,z6]),(0,[z345,z7,z3,z4,z5,z6,z51]),(0,[z1,z7,z3,z4,z106,z5,z6]),(0,[z1,z7,z3,z4,z172,z5,z6]),(1,[z1,z70,z3,z4,z5,z33]),(0,[z1,z26,z7,z14,z3,z5,z6]),(1,[z1,z450,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z5,z6,z451])],[(0,[z1,z37,z81,z3,z4,z5,z6]),(0,[z1,z55,z7,z4,z82,z5,z6]),(0,[z452,z1,z7,z3,z4,z5,z6]),(0,[z453,z1,z7,z3,z4,z5,z6])],[(0,[z1,z454,z7,z3,z4,z5,z6])],[(0,[z1,z455,z7,z3,z4,z5,z6]),(0,[z1,z456,z7,z3,z4,z5,z6]),(0,[z1,z7,z457,z3,z4,z5,z6])],[],[(0,[z1,z458,z7,z3,z4,z5,z6]),(0,[z1,z459,z7,z3,z4,z5,z6]),(1,[z1,z168,z3,z4,z172,z6]),(0,[z1,z7,z36,z3,z4,z5,z6])],[(0,[z1,z460,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z461]),(0,[z1,z7,z462,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z463,z6]),(0,[z1,z450,z7,z3,z4,z5,z6]),(1,[z45,z1,z7,z3,z4,z170])]],
   [[(0,[z464,z1,z7,z3,z4,z5,z6]),(0,[z1,z465,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z466]),(1,[z376,z7,z3,z4,z5,z6])],[(0,[z467,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z276,z4,z5,z59,z6])],[(0,[z1,z468,z7,z3,z4,z5,z6]),(0,[z1,z12,z3,z4,z31,z5,z6]),(1,[z1,z2,z3,z4,z120,z6]),(0,[z1,z7,z3,z4,z253,z5,z6]),(0,[z1,z469,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z470,z6])],[(0,[z471,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z472,z6])],[(0,[z1,z473,z7,z3,z4,z5,z6]),(0,[z219,z247,z7,z3,z4,z5,z6]),(0,[z1,z421,z7,z3,z4,z5,z6]),(0,[z1,z474,z7,z3,z4,z5,z6]),(1,[z1,z54,z55,z7,z5,z6]),(0,[z1,z475,z7,z3,z4,z5,z6])],[(1,[z1,z7,z128,z4,z5,z6]),(0,[z69,z1,z3,z4,z31,z5,z6]),(0,[z79,z89,z7,z3,z4,z5,z6]),(0,[z143,z7,z3,z4,z5,z190,z6]),(0,[z1,z476,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z477,z6]),(0,[z1,z7,z3,z388,z5,z57,z6]),(0,[z1,z7,z3,z478,z4,z5,z6])],[(0,[z1,z7,z3,z479,z4,z5,z6]),(0,[z1,z480,z7,z3,z4,z5,z6]),(1,[z1,z7,z4,z5,z6,z17])],[(0,[z1,z7,z481,z3,z4,z5,z6]),(0,[z482,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z483,z6]),(1,[z157,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z484,z3,z4,z5,z6]),(1,[z10,z7,z3,z4,z154,z6]),(0,[z485,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z29,z4,z5,z18])],[(0,[z1,z7,z3,z4,z5,z486,z6]),(0,[z1,z487,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z488,z6]),(0,[z1,z7,z3,z489,z4,z5,z6]),(0,[z1,z7,z490,z3,z4,z5,z6])],[],[(1,[z1,z421,z3,z4,z5,z6]),(0,[z1,z491,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z492,z5,z6]),(0,[z493,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z494,z5,z6])],[(0,[z1,z181,z7,z12,z3,z5,z6]),(1,[z1,z7,z14,z15,z5,z6])],[(0,[z1,z7,z3,z495,z4,z5,z6]),(0,[z1,z496,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z497])],[(1,[z69,z78,z3,z4,z5,z6]),(0,[z498,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z499,z6]),(1,[z1,z7,z364,z4,z5,z6]),(0,[z1,z7,z3,z4,z500,z5,z6]),(0,[z1,z501,z7,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z71,z6]),(0,[z1,z3,z171,z4,z379,z5,z6]),(0,[z1,z7,z502,z3,z4,z5,z6]),(0,[z503,z1,z7,z3,z4,z5,z6])],[(0,[z504,z1,z7,z3,z4,z5,z6]),(0,[z1,z14,z3,z4,z253,z5,z6]),(0,[z1,z7,z3,z505,z4,z5,z6]),(0,[z1,z7,z506,z3,z4,z5,z6]),(0,[z45,z1,z204,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z299,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z507]),(0,[z7,z3,z4,z106,z82,z5,z6]),(0,[z1,z3,z4,z5,z71,z6,z33]),(0,[z45,z1,z26,z7,z3,z4,z6])],[(0,[z1,z7,z3,z4,z5,z6,z272]),(0,[z143,z11,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z508,z5,z6]),(0,[z1,z509,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z510,z5,z6]),(0,[z1,z7,z3,z4,z511,z5,z6])],[(0,[z1,z512,z7,z3,z4,z5,z6]),(1,[z333,z7,z3,z4,z5,z6])],[(0,[z11,z7,z90,z3,z4,z5,z6]),(0,[z1,z7,z513,z3,z4,z5,z6]),(0,[z1,z7,z514,z3,z4,z5,z6]),(0,[z1,z7,z12,z3,z296,z5,z6]),(0,[z1,z3,z4,z5,z231,z6,z51]),(0,[z1,z7,z3,z4,z5,z6,z515])],[(1,[z1,z7,z3,z179,z5,z6]),(0,[z1,z7,z3,z4,z516,z5,z6]),(0,[z1,z7,z3,z4,z517,z5,z6]),(0,[z1,z7,z3,z4,z5,z518,z6]),(0,[z1,z7,z3,z4,z5,z519,z6]),(0,[z1,z7,z520,z3,z4,z5,z6])],[]],
   [[(0,[z1,z7,z3,z4,z5,z6,z521]),(0,[z1,z7,z3,z4,z5,z522,z6]),(0,[z1,z7,z3,z523,z4,z5,z6])],[(0,[z1,z524,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z525]),(0,[z143,z1,z7,z3,z4,z5,z80]),(0,[z1,z168,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z526,z5,z6])],[(0,[z1,z133,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z527,z4,z5,z6]),(0,[z1,z7,z3,z4,z528,z5,z6])],[(0,[z529,z1,z7,z3,z4,z5,z6]),(0,[z69,z1,z3,z4,z172,z5,z6]),(0,[z1,z7,z530,z3,z4,z5,z6]),(0,[z531,z1,z7,z3,z4,z5,z6]),(0,[z1,z532,z7,z3,z4,z5,z6]),(0,[z1,z533,z7,z3,z4,z5,z6]),(0,[z1,z7,z534,z3,z4,z5,z6])],[(0,[z1,z7,z14,z4,z82,z5,z6]),(1,[z1,z7,z268,z4,z5,z6])],[(0,[z535,z1,z7,z3,z4,z5,z6]),(0,[z69,z1,z7,z3,z239,z5,z6]),(0,[z69,z79,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z536]),(0,[z1,z7,z3,z4,z5,z537,z6])],[(0,[z1,z7,z538,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z71,z80]),(1,[z7,z3,z4,z200,z5,z6]),(0,[z539,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z6,z192])],[(0,[z540,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z541])]],
   [[(0,[z1,z542,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z543,z4,z5,z6]),(0,[z1,z7,z544,z3,z4,z5,z6]),(0,[z545,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z546]),(0,[z1,z7,z547,z3,z4,z5,z6]),(0,[z548,z1,z7,z3,z4,z5,z6]),(0,[z10,z1,z7,z3,z4,z5,z145])],[(0,[z1,z7,z3,z549,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z550,z6]),(0,[z1,z7,z3,z4,z5,z51,z33]),(0,[z551,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z57,z6]),(0,[z552,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z553]),(0,[z554,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z38,z14,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z555,z6]),(0,[z1,z204,z7,z14,z3,z5,z6]),(0,[z1,z7,z556,z3,z4,z5,z6])],[(0,[z0,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z557,z6]),(0,[z1,z7,z3,z4,z558,z5,z6]),(0,[z1,z559,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z560,z6]),(0,[z1,z561,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z562,z5,z6]),(0,[z1,z7,z3,z72,z5,z59,z6])],[(0,[z1,z7,z563,z3,z4,z5,z6]),(1,[z1,z7,z186,z4,z16,z6]),(0,[z564,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z565,z4,z5,z6])],[(0,[z7,z3,z171,z4,z296,z5,z6]),(0,[z1,z7,z3,z4,z31,z5,z6]),(0,[z1,z7,z566,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z49,z6]),(0,[z1,z7,z3,z296,z31,z5,z6]),(0,[z1,z7,z3,z4,z5,z567,z6]),(0,[z1,z7,z3,z4,z5,z568,z6]),(0,[z1,z569,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z570,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z571,z6]),(1,[z1,z7,z3,z5,z6,z125])],[(1,[z1,z7,z3,z4,z221,z6]),(0,[z45,z1,z7,z3,z4,z190,z6]),(0,[z1,z572,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z82,z5,z6]),(0,[z1,z7,z3,z4,z244,z5,z6]),(0,[z1,z7,z573,z3,z4,z5,z6]),(0,[z1,z574,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z18])],[(0,[z575,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z171,z31,z5,z6]),(0,[z1,z7,z3,z4,z576,z5,z6]),(0,[z45,z1,z7,z3,z29,z4,z5])],[(0,[z69,z1,z11,z3,z4,z5,z6]),(1,[z247,z7,z3,z296,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z577]),(0,[z1,z81,z3,z4,z82,z5,z6]),(0,[z1,z578,z7,z3,z4,z5,z6]),(0,[z1,z7,z579,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z389,z18])],[(0,[z1,z7,z3,z580,z4,z5,z6])],[(0,[z1,z581,z7,z3,z4,z5,z6]),(0,[z7,z90,z3,z163,z4,z5,z6]),(0,[z1,z7,z3,z582,z4,z5,z6]),(1,[z1,z204,z7,z3,z5,z18])],[(0,[z45,z1,z7,z186,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z120,z6]),(0,[z1,z583,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z584,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z585,z6]),(0,[z1,z7,z38,z3,z4,z5,z6]),(0,[z1,z108,z7,z12,z3,z5,z6]),(0,[z1,z586,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z587,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z56,z6]),(0,[z45,z1,z7,z27,z3,z4,z6]),(0,[z1,z7,z3,z4,z588,z5,z6]),(0,[z1,z589,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z163,z4,z5,z6]),(0,[z590,z1,z7,z3,z4,z5,z6]),(0,[z1,z591,z7,z3,z4,z5,z6])],[(1,[z1,z7,z3,z4,z5,z260]),(0,[z1,z7,z3,z4,z5,z592,z6])],[(0,[z1,z7,z3,z4,z5,z593,z6]),(0,[z1,z108,z3,z4,z31,z5,z6]),(0,[z1,z594,z7,z3,z4,z5,z6])],[(0,[z1,z595,z7,z3,z4,z5,z6]),(0,[z1,z55,z7,z4,z16,z5,z6])],[(0,[z1,z7,z596,z3,z4,z5,z6]),(0,[z1,z7,z186,z3,z4,z57,z6])],[(0,[z1,z7,z3,z4,z597,z5,z6]),(0,[z45,z1,z7,z3,z4,z6,z170])],[(1,[z1,z7,z3,z4,z5,z272]),(0,[z598,z1,z7,z3,z4,z5,z6]),(1,[z89,z7,z90,z4,z5,z6]),(0,[z345,z1,z7,z3,z4,z5,z80]),(0,[z1,z37,z7,z19,z3,z5,z6]),(0,[z1,z599,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z388,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z600,z6]),(0,[z1,z601,z7,z3,z4,z5,z6]),(0,[z1,z54,z7,z3,z31,z5,z6]),(0,[z602,z1,z7,z3,z4,z5,z6]),(0,[z1,z204,z7,z3,z4,z5,z18]),(0,[z1,z603,z7,z3,z4,z5,z6])],[(0,[z0,z11,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z604,z5,z6]),(0,[z1,z7,z3,z605,z4,z5,z6])],[(0,[z1,z7,z3,z4,z606,z5,z6]),(0,[z1,z7,z3,z4,z5,z231,z6]),(0,[z607,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z608,z4,z5,z6]),(0,[z1,z450,z7,z3,z4,z5,z57])],[(0,[z1,z7,z609,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z610,z5,z6]),(0,[z1,z7,z3,z4,z5,z611,z6])],[(0,[z1,z7,z3,z4,z5,z249,z6]),(0,[z1,z612,z7,z3,z4,z5,z6]),(0,[z1,z24,z7,z3,z4,z57,z6]),(0,[z1,z7,z4,z16,z5,z57,z6])],[(0,[z613,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z614,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z615])],[(0,[z1,z7,z3,z4,z5,z616,z6]),(0,[z1,z617,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z618,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z619,z4,z5,z6]),(0,[z1,z7,z3,z4,z620,z5,z6]),(0,[z1,z7,z3,z4,z5,z80,z6]),(0,[z143,z1,z7,z3,z4,z114,z6]),(0,[z1,z7,z3,z4,z5,z6,z621]),(0,[z41,z1,z7,z3,z4,z5,z6]),(0,[z1,z622,z7,z3,z4,z5,z6])],[(0,[z1,z7,z38,z163,z4,z5,z6]),(0,[z1,z7,z3,z4,z296,z5,z6]),(0,[z1,z7,z3,z4,z5,z623,z6]),(0,[z1,z7,z624,z3,z4,z5,z6]),(0,[z1,z55,z7,z4,z15,z5,z6]),(0,[z1,z7,z4,z5,z84,z6,z130]),(0,[z1,z7,z3,z4,z5,z6,z625])],[(0,[z1,z626,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z627,z6]),(0,[z628,z1,z7,z3,z4,z5,z6]),(0,[z1,z629,z7,z3,z4,z5,z6]),(0,[z1,z630,z7,z3,z4,z5,z6])],[(1,[z1,z3,z4,z379,z5,z6]),(0,[z10,z143,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z91,z6]),(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z1,z631,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z632,z6])],[(0,[z633,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z90,z4,z82,z5,z6]),(1,[z1,z279,z7,z3,z4,z6]),(1,[z1,z7,z4,z58,z5,z6]),(0,[z1,z7,z3,z4,z5,z30,z6])],[(0,[z1,z7,z3,z4,z634,z5,z6]),(0,[z189,z1,z7,z3,z4,z154,z6])],[(0,[z1,z156,z7,z3,z4,z5,z6]),(0,[z1,z38,z3,z4,z82,z5,z6]),(0,[z1,z2,z7,z3,z4,z172,z6]),(0,[z1,z7,z186,z4,z16,z5,z6])],[(0,[z1,z7,z3,z4,z5,z635,z6]),(0,[z1,z636,z7,z3,z4,z5,z6]),(0,[z1,z637,z7,z3,z4,z5,z6]),(0,[z1,z204,z7,z3,z4,z5,z30])]],
   [[(0,[z189,z1,z7,z3,z4,z5,z6]),(0,[z1,z70,z7,z3,z4,z5,z33]),(0,[z1,z638,z7,z3,z4,z5,z6])],[(0,[z1,z639,z7,z3,z4,z5,z6]),(0,[z10,z1,z7,z3,z4,z154,z6]),(0,[z1,z7,z3,z4,z5,z640,z6]),(0,[z1,z7,z3,z4,z641,z5,z6]),(0,[z1,z7,z3,z4,z5,z642,z6]),(0,[z1,z7,z3,z4,z5,z643,z6]),(0,[z1,z7,z644,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z645,z5,z6]),(0,[z1,z7,z646,z3,z4,z5,z6])],[(0,[z69,z7,z78,z3,z4,z5,z6]),(0,[z1,z647,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z648,z6]),(0,[z1,z7,z3,z4,z5,z649,z6]),(0,[z1,z7,z3,z4,z5,z6,z650]),(0,[z1,z7,z3,z4,z5,z6,z651]),(0,[z1,z7,z3,z4,z5,z6,z652])],[(0,[z69,z1,z3,z4,z82,z5,z6]),(0,[z1,z653,z7,z3,z4,z5,z6]),(0,[z1,z7,z654,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z25,z6])],[(0,[z1,z7,z3,z4,z4,z5,z6]),(0,[z10,z1,z7,z3,z4,z5,z6]),(0,[z1,z156,z3,z4,z5,z6,z51]),(0,[z1,z7,z3,z4,z5,z6,z655])],[(0,[z69,z1,z7,z116,z4,z5,z6]),(0,[z1,z7,z656,z3,z4,z5,z6]),(0,[z1,z297,z7,z3,z4,z5,z6]),(0,[z1,z657,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z658]),(0,[z1,z7,z3,z4,z659,z5,z6]),(0,[z1,z7,z3,z4,z660,z5,z6]),(0,[z334,z7,z3,z4,z172,z5,z6]),(0,[z1,z7,z3,z661,z4,z5,z6]),(0,[z1,z204,z7,z3,z4,z46,z5]),(0,[z1,z7,z3,z4,z662,z5,z6])],[(0,[z1,z7,z663,z3,z4,z5,z6]),(0,[z1,z664,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z665,z6]),(1,[z1,z35,z7,z4,z5,z130])],[(0,[z1,z297,z3,z171,z4,z5,z6]),(1,[z334,z7,z3,z4,z5,z6]),(0,[z1,z109,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z666,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z172,z190,z6]),(0,[z1,z7,z3,z4,z46,z5,z80]),(0,[z1,z667,z7,z3,z4,z5,z6]),(1,[z1,z37,z38,z4,z5,z6]),(0,[z7,z3,z4,z346,z31,z5,z6]),(0,[z1,z7,z3,z4,z668,z5,z6]),(0,[z1,z7,z669,z3,z4,z5,z6]),(0,[z670,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z671])],[(0,[z1,z7,z78,z3,z4,z5,z6]),(0,[z1,z672,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z346,z5,z6]),(0,[z673,z1,z7,z3,z4,z5,z6]),(0,[z1,z55,z7,z4,z5,z84,z6]),(0,[z45,z1,z35,z7,z3,z4,z5])],[(0,[z1,z674,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z675,z6]),(0,[z1,z7,z676,z3,z4,z5,z6]),(0,[z1,z7,z3,z677,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z678]),(0,[z679,z1,z7,z3,z4,z5,z6]),(0,[z376,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z680])],[(0,[z681,z1,z7,z3,z4,z5,z6]),(0,[z1,z682,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z683,z4,z5,z6]),(0,[z1,z684,z7,z3,z4,z5,z6]),(0,[z1,z181,z7,z3,z31,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z685]),(0,[z1,z7,z3,z4,z5,z6,z389]),(1,[z1,z7,z3,z29,z5,z30])],[(0,[z1,z181,z3,z4,z82,z5,z6]),(0,[z1,z2,z7,z3,z4,z120,z6]),(0,[z1,z7,z3,z4,z5,z6,z686]),(0,[z1,z7,z14,z4,z16,z5,z6]),(0,[z1,z54,z7,z3,z5,z30,z6]),(0,[z1,z687,z7,z3,z4,z5,z6])],[(0,[z247,z7,z3,z4,z296,z5,z6]),(0,[z1,z7,z688,z3,z4,z5,z6]),(0,[z1,z7,z85,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z181,z3,z4,z5,z6]),(0,[z1,z689,z7,z3,z4,z5,z6]),(0,[z1,z37,z7,z4,z82,z5,z6])],[(0,[z1,z7,z690,z3,z4,z5,z6]),(0,[z1,z691,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z118]),(0,[z1,z7,z3,z4,z5,z692,z6]),(0,[z1,z7,z3,z4,z72,z5,z6]),(0,[z1,z7,z276,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z693])],[(0,[z694,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z33]),(0,[z1,z7,z3,z4,z5,z695,z6]),(0,[z1,z7,z3,z4,z5,z6,z696])],[(1,[z345,z7,z3,z4,z5,z51]),(0,[z1,z7,z3,z4,z697,z5,z6])],[(0,[z0,z1,z70,z3,z4,z5,z6]),(0,[z698,z1,z7,z3,z4,z5,z6]),(0,[z333,z1,z7,z3,z4,z5,z6])],[(0,[z1,z699,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z700,z6]),(0,[z1,z701,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z702])],[(0,[z79,z1,z7,z3,z4,z5,z6]),(0,[z1,z703,z7,z3,z4,z5,z6]),(0,[z1,z37,z3,z4,z31,z5,z6])],[(0,[z1,z7,z704,z3,z4,z5,z6]),(0,[z1,z705,z7,z3,z4,z5,z6]),(0,[z706,z1,z7,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z181,z128,z4,z5,z6]),(0,[z1,z707,z3,z4,z5,z6]),(0,[z1,z7,z3,z708,z5,z6]),(0,[z1,z7,z3,z5,z6,z709])],[(0,[z1,z7,z710,z4,z5,z6]),(0,[z385,z7,z3,z4,z190,z6])],[(0,[z1,z7,z3,z4,z5,z711]),(0,[z3,z4,z106,z149,z5,z6]),(0,[z45,z1,z7,z402,z3,z4])],[(0,[z1,z7,z3,z712,z5,z6]),(0,[z1,z713,z7,z14,z5,z6])],[(0,[z1,z7,z116,z239,z5,z6]),(0,[z1,z7,z3,z4,z714,z6]),(0,[z334,z7,z3,z4,z49,z6]),(0,[z715,z7,z3,z4,z5,z6]),(0,[z1,z24,z7,z209,z5,z6])],[(0,[z1,z7,z3,z4,z716,z6]),(0,[z7,z3,z4,z5,z190,z272]),(0,[z1,z717,z3,z4,z5,z6]),(0,[z81,z4,z106,z82,z5,z6]),(0,[z1,z7,z3,z4,z5,z718])],[],[(0,[z1,z3,z4,z5,z719,z6]),(0,[z1,z7,z3,z4,z114,z51]),(0,[z1,z7,z4,z720,z5,z6])]],
   [[(0,[z1,z721,z3,z4,z5,z6])],[(0,[z0,z3,z4,z200,z5,z6]),(0,[z7,z3,z4,z154,z722,z6]),(0,[z376,z7,z3,z4,z114,z6]),(0,[z7,z3,z4,z723,z5,z6])],[(0,[z1,z7,z724,z4,z5,z6]),(0,[z1,z7,z725,z4,z5,z6]),(0,[z45,z1,z7,z3,z4,z507]),(0,[z45,z1,z7,z3,z4,z522]),(0,[z1,z35,z279,z7,z4,z130])],[(0,[z1,z133,z116,z4,z5,z6]),(0,[z1,z279,z7,z3,z4,z6]),(0,[z1,z726,z3,z4,z5,z6]),(0,[z1,z7,z27,z3,z6,z655])],[(0,[z1,z156,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z727]),(0,[z1,z7,z3,z4,z5,z728]),(0,[z341,z7,z90,z4,z5,z6]),(0,[z1,z729,z3,z4,z5,z6]),(0,[z1,z108,z730,z3,z5,z6]),(0,[z7,z3,z4,z5,z731,z6]),(0,[z7,z3,z4,z732,z5,z6]),(0,[z733,z7,z3,z4,z5,z6]),(0,[z734,z157,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z735])],[(0,[z421,z3,z4,z5,z6,z51]),(0,[z736,z7,z3,z4,z5,z6]),(0,[z1,z87,z7,z205,z4,z6])],[(0,[z1,z7,z3,z737,z5,z6]),(0,[z1,z7,z205,z4,z6,z389])],[(0,[z7,z738,z3,z4,z5,z6]),(0,[z89,z7,z739,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z740]),(0,[z333,z181,z3,z4,z5,z6]),(0,[z1,z741,z7,z3,z4,z6]),(0,[z1,z7,z12,z268,z5,z6]),(0,[z742,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z743])],[(0,[z1,z181,z3,z179,z5,z6]),(0,[z7,z3,z4,z744,z5,z6])],[(0,[z1,z7,z4,z5,z6,z745]),(0,[z143,z7,z3,z4,z5,z80]),(0,[z1,z24,z7,z4,z746,z6]),(0,[z1,z7,z36,z4,z5,z139]),(0,[z1,z7,z3,z747,z59,z6])],[(0,[z1,z7,z3,z748,z5,z6]),(0,[z1,z7,z3,z4,z749,z6]),(0,[z10,z7,z3,z4,z154,z118]),(0,[z7,z3,z4,z5,z750,z51])],[(0,[z1,z3,z495,z31,z5,z6]),(0,[z1,z7,z3,z751,z5,z6]),(0,[z10,z7,z3,z4,z114,z6]),(0,[z1,z7,z3,z752,z5,z6]),(0,[z1,z7,z3,z4,z5,z753])],[(0,[z79,z7,z739,z4,z5,z6]),(0,[z1,z754,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z755,z6]),(0,[z1,z756,z3,z4,z5,z6]),(0,[z757,z7,z3,z4,z5,z6])],[(0,[z1,z297,z3,z31,z5,z6]),(0,[z1,z37,z38,z4,z5,z6]),(0,[z1,z7,z3,z4,z758,z6]),(0,[z759,z7,z3,z4,z5,z6]),(0,[z760,z1,z7,z3,z4,z6])]],
   [[(0,[z1,z7,z3,z4,z761,z6]),(0,[z1,z297,z762,z4,z5,z6]),(0,[z1,z7,z27,z3,z747,z6])],[(0,[z1,z7,z3,z4,z5,z763]),(0,[z1,z3,z4,z764,z5,z6]),(0,[z765,z7,z3,z4,z5,z6]),(0,[z766,z7,z3,z4,z5,z6]),(0,[z1,z730,z3,z31,z5,z6])],[(0,[z143,z7,z3,z4,z5,z750])],[(0,[z1,z7,z3,z767,z5,z6]),(0,[z334,z7,z3,z4,z5,z718]),(0,[z1,z7,z624,z14,z5,z6]),(0,[z1,z7,z205,z5,z30,z6])],[(0,[z1,z7,z3,z4,z5,z768]),(0,[z143,z7,z3,z4,z91,z80])],[(0,[z1,z7,z3,z769,z5,z6]),(0,[z1,z770,z3,z4,z5,z6]),(0,[z1,z181,z12,z364,z5,z6]),(0,[z1,z7,z3,z771,z5,z6]),(1,[z1,z3,z4,z5,z772]),(0,[z1,z773,z7,z4,z5,z6])],[(0,[z0,z1,z3,z244,z5,z6]),(0,[z1,z473,z4,z82,z5,z6]),(0,[z1,z774,z7,z3,z4,z6]),(0,[z775,z1,z7,z3,z4,z5])],[(0,[z11,z3,z4,z379,z5,z6]),(0,[z1,z7,z85,z3,z6,z192])]],
   [[(0,[z69,z3,z4,z379,z5,z6]),(0,[z7,z3,z171,z776,z5,z6]),(0,[z1,z3,z4,z777,z5,z6])],[(0,[z1,z7,z3,z4,z5,z778]),(0,[z1,z7,z3,z4,z779,z6]),(0,[z531,z7,z3,z4,z190,z6]),(0,[z10,z156,z3,z4,z5,z6]),(0,[z45,z157,z7,z3,z4,z170])],[(0,[z1,z7,z3,z4,z780,z6])],[(0,[z1,z7,z3,z4,z5,z750]),(0,[z1,z37,z38,z19,z5,z6]),(0,[z1,z7,z781,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z782]),(0,[z7,z3,z4,z783,z5,z6]),(0,[z1,z3,z4,z5,z71,z772])],[(0,[z69,z586,z3,z4,z5,z6]),(0,[z376,z7,z3,z4,z5,z80]),(0,[z1,z664,z3,z31,z5,z6])],[(0,[z1,z7,z3,z4,z784,z6]),(0,[z1,z3,z543,z31,z5,z6]),(0,[z1,z268,z4,z82,z5,z6]),(0,[z1,z7,z3,z4,z5,z785]),(0,[z1,z7,z36,z4,z5,z84]),(0,[z1,z26,z7,z3,z59,z6])],[(0,[z1,z7,z3,z239,z5,z6]),(0,[z1,z7,z3,z4,z5,z786]),(0,[z1,z713,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z787]),(0,[z1,z7,z4,z5,z6,z788])]],
   [[(0,[z1,z789,z3,z4,z5,z6]),(0,[z790,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z791,z6])],[(0,[z7,z3,z4,z221,z6,z51]),(0,[z1,z3,z4,z5,z6,z792])],[(0,[z334,z7,z3,z4,z190,z6]),(0,[z1,z7,z3,z5,z6,z793]),(0,[z1,z7,z794,z4,z5,z6])],[(0,[z1,z7,z19,z3,z5,z6]),(0,[z1,z795,z3,z4,z5,z6])],[(0,[z52,z7,z3,z4,z5,z260]),(0,[z1,z7,z4,z6,z17,z389])],[(0,[z1,z7,z3,z4,z5,z796]),(0,[z1,z797,z7,z3,z5,z6]),(0,[z1,z7,z795,z4,z5,z6])],[(0,[z69,z407,z3,z4,z5,z6]),(0,[z345,z156,z3,z4,z5,z51]),(0,[z1,z3,z4,z253,z5,z6])],[(0,[z333,z7,z163,z4,z5,z6]),(0,[z1,z7,z798,z3,z5,z6]),(0,[z1,z3,z4,z799,z5,z6]),(0,[z1,z800,z7,z3,z4,z6]),(0,[z1,z3,z4,z5,z772,z33])]],
   [[(0,[z41,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z801]),(0,[z1,z3,z4,z5,z6,z802]),(0,[z1,z7,z3,z803,z5,z6])],[(0,[z1,z133,z3,z804,z5,z6]),(0,[z1,z699,z3,z4,z172,z6])],[(0,[z333,z7,z90,z4,z5,z6]),(0,[z1,z450,z24,z7,z4,z57]),(0,[z1,z35,z7,z85,z5,z130]),(0,[z805,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z806]),(0,[z1,z181,z730,z3,z5,z6]),(0,[z1,z7,z4,z5,z84,z401]),(0,[z1,z7,z807,z4,z5,z6]),(0,[z1,z204,z7,z205,z5,z6]),(0,[z1,z3,z4,z5,z808,z6])],[(0,[z1,z7,z3,z5,z6,z809]),(0,[z45,z7,z3,z4,z190,z51]),(0,[z1,z7,z3,z810,z5,z6]),(0,[z1,z87,z7,z3,z4,z6])],[],[(0,[z1,z128,z4,z31,z5,z6]),(0,[z1,z7,z128,z239,z5,z6]),(0,[z79,z7,z128,z4,z5,z6]),(0,[z1,z70,z3,z4,z5,z272]),(0,[z1,z37,z268,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z772]),(0,[z1,z7,z276,z4,z5,z6]),(0,[z1,z279,z7,z85,z3,z6])],[(0,[z1,z7,z3,z811,z5,z6]),(0,[z1,z812,z7,z3,z4,z5]),(0,[z813,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z738,z3,z4,z5,z6]),(0,[z1,z814,z3,z4,z5,z6]),(0,[z403,z7,z3,z171,z5,z6]),(0,[z1,z7,z3,z209,z5,z6]),(0,[z1,z35,z7,z5,z125,z130])],[(0,[z69,z1,z3,z244,z5,z6]),(0,[z1,z7,z3,z4,z5,z815]),(0,[z1,z7,z4,z5,z816,z130])],[(0,[z1,z7,z3,z817,z5,z6]),(0,[z1,z7,z818,z4,z5,z6]),(0,[z1,z81,z4,z82,z5,z6]),(0,[z52,z7,z3,z4,z819,z6]),(0,[z1,z7,z85,z3,z5,z6]),(0,[z1,z820,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z821])],[(0,[z69,z3,z4,z106,z5,z6]),(0,[z7,z3,z4,z5,z6,z750])],[(0,[z1,z7,z822,z4,z5,z6]),(0,[z1,z7,z3,z823,z5,z6]),(0,[z1,z7,z824,z4,z5,z6]),(0,[z825,z7,z3,z4,z5,z6]),(0,[z826,z7,z3,z4,z5,z6])],[(0,[z1,z7,z827,z4,z5,z6]),(0,[z345,z7,z3,z4,z5,z750]),(0,[z1,z3,z4,z828,z120,z6])],[(0,[z1,z3,z4,z299,z5,z6]),(0,[z1,z7,z4,z5,z6,z816]),(0,[z1,z7,z4,z58,z5,z60])],[(0,[z7,z3,z4,z106,z5,z6]),(0,[z1,z109,z3,z4,z5,z6])]],
   [[(0,[z69,z78,z3,z239,z5,z6]),(0,[z7,z3,z4,z5,z249,z6]),(0,[z41,z37,z3,z4,z5,z6]),(0,[z1,z181,z12,z3,z5,z6]),(0,[z1,z7,z27,z3,z72,z6]),(0,[z829,z1,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z830]),(0,[z831,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z832,z6]),(0,[z1,z450,z24,z7,z3,z4])],[(0,[z7,z3,z171,z239,z5,z6]),(0,[z1,z7,z3,z4,z5,z833]),(0,[z1,z181,z12,z268,z5,z6]),(0,[z1,z7,z834,z4,z5,z6]),(0,[z1,z26,z7,z3,z60,z59]),(0,[z1,z7,z276,z72,z5,z6])],[(0,[z1,z7,z3,z835,z5,z6]),(0,[z1,z7,z3,z4,z5,z836]),(0,[z1,z3,z4,z837,z5,z6]),(0,[z1,z7,z3,z4,z5,z118]),(0,[z1,z7,z3,z72,z568,z6]),(0,[z838,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z839]),(0,[z45,z1,z7,z3,z4,z658]),(0,[z1,z279,z7,z36,z3,z4])],[(0,[z1,z109,z38,z4,z5,z6]),(0,[z1,z3,z4,z840,z5,z6]),(0,[z1,z7,z3,z4,z746,z6])],[(0,[z69,z474,z3,z4,z5,z6]),(0,[z1,z7,z3,z776,z5,z6]),(0,[z1,z7,z3,z4,z841,z6])]],
   [[(0,[z1,z24,z7,z4,z56,z57]),(0,[z842,z7,z3,z4,z5,z6])],[(0,[z69,z481,z3,z4,z5,z6]),(0,[z1,z3,z4,z172,z176,z6]),(0,[z1,z843,z3,z4,z5,z6]),(0,[z1,z26,z7,z3,z21,z6]),(0,[z1,z7,z3,z4,z5,z816])],[(0,[z1,z7,z844,z4,z5,z6]),(0,[z1,z3,z4,z845,z5,z6]),(0,[z1,z7,z4,z5,z846,z6])],[],[(0,[z1,z7,z3,z847,z5,z6]),(0,[z1,z7,z3,z4,z154,z145]),(0,[z1,z7,z3,z4,z5,z848])],[(0,[z1,z156,z3,z4,z5,z272]),(0,[z11,z738,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z828,z6]),(0,[z1,z7,z3,z4,z5,z849])],[(0,[z69,z738,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z850,z6]),(1,[z1,z7,z3,z747,z6])],[(0,[z1,z7,z3,z4,z5,z851]),(0,[z1,z7,z3,z4,z852,z6]),(0,[z7,z3,z4,z5,z853,z6]),(0,[z854,z7,z3,z4,z5,z6]),(0,[z1,z7,z14,z405,z5,z6])]],
   [[(0,[z189,z7,z3,z4,z722,z6])],[],[(0,[z1,z7,z855,z4,z5,z6]),(0,[z856,z7,z3,z4,z5,z6]),(0,[z857,z7,z3,z4,z5,z6])],[(0,[z11,z3,z4,z299,z5,z6]),(0,[z189,z7,z3,z4,z190,z6])],[(0,[z69,z3,z4,z299,z5,z6]),(0,[z7,z3,z4,z346,z5,z6]),(0,[z1,z3,z4,z858,z5,z6])],[(0,[z1,z7,z762,z4,z5,z6]),(1,[z1,z795,z4,z5,z6])],[(0,[z1,z7,z859,z4,z5,z6]),(0,[z69,z599,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z860]),(0,[z1,z7,z861,z4,z5,z6]),(0,[z1,z14,z253,z15,z5,z6]),(0,[z1,z109,z14,z15,z5,z6])],[(0,[z1,z7,z3,z4,z5,z862]),(0,[z69,z513,z3,z4,z5,z6]),(0,[z1,z863,z3,z4,z5,z6]),(0,[z1,z7,z4,z864,z5,z6]),(0,[z1,z7,z3,z244,z5,z6]),(0,[z1,z7,z3,z6,z125,z192])]],
   [[(0,[z1,z7,z3,z239,z49,z6]),(0,[z1,z3,z4,z172,z221,z6]),(0,[z3,z4,z346,z379,z5,z6]),(0,[z1,z3,z4,z5,z865,z6]),(0,[z45,z1,z7,z3,z4,z9]),(0,[z333,z81,z4,z82,z5,z6])],[(0,[z11,z7,z3,z4,z5,z118]),(0,[z376,z7,z3,z4,z5,z145])],[(0,[z1,z7,z3,z239,z221,z6]),(0,[z69,z7,z3,z4,z5,z118]),(0,[z1,z512,z3,z31,z5,z6]),(0,[z1,z866,z7,z3,z4,z5]),(0,[z867,z7,z3,z4,z5,z6]),(0,[z1,z204,z7,z3,z5,z709])],[(0,[z219,z7,z3,z776,z5,z6]),(0,[z868,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z388,z5,z56])],[(0,[z1,z7,z3,z869,z5,z6]),(0,[z1,z7,z3,z870,z5,z6]),(0,[z1,z7,z4,z5,z6,z871]),(0,[z1,z7,z3,z872,z5,z6])],[(0,[z1,z297,z3,z179,z5,z6]),(0,[z7,z3,z4,z722,z5,z6]),(0,[z1,z7,z3,z4,z114,z80]),(0,[z1,z7,z873,z4,z5,z6]),(0,[z1,z874,z7,z3,z5,z6])],[(0,[z1,z81,z795,z4,z5,z6])],[(0,[z1,z181,z19,z3,z5,z6]),(0,[z1,z450,z7,z3,z388,z5]),(1,[z1,z7,z3,z5,z709])]],
   [[],[(0,[z10,z7,z3,z4,z154,z145]),(0,[z1,z108,z3,z31,z5,z6]),(0,[z1,z7,z3,z4,z5,z875]),(0,[z1,z7,z3,z4,z5,z876]),(0,[z1,z7,z3,z877,z5,z6]),(0,[z1,z7,z186,z4,z746,z6])],[],[(0,[z1,z7,z3,z239,z5,z260]),(0,[z0,z3,z4,z106,z5,z6]),(0,[z7,z90,z4,z634,z5,z6]),(0,[z1,z7,z3,z4,z878,z6]),(0,[z1,z879,z7,z3,z4,z6]),(0,[z334,z7,z3,z4,z5,z849]),(0,[z1,z7,z4,z16,z164,z6]),(0,[z1,z271,z26,z7,z3,z59])],[(0,[z1,z7,z3,z880,z5,z6]),(0,[z1,z204,z7,z3,z389,z18])],[(0,[z219,z3,z171,z379,z5,z6]),(0,[z208,z7,z3,z4,z5,z51]),(0,[z1,z7,z3,z4,z6,z881]),(0,[z1,z109,z268,z4,z5,z6]),(0,[z7,z3,z4,z5,z882,z6]),(0,[z1,z271,z26,z7,z3,z4]),(0,[z1,z7,z3,z4,z6,z389])],[(0,[z7,z3,z4,z5,z883,z6]),(0,[z1,z7,z205,z4,z5,z6]),(0,[z884,z7,z3,z4,z5,z6])],[(0,[z247,z7,z3,z239,z5,z6]),(0,[z1,z3,z4,z5,z231,z6]),(0,[z1,z885,z3,z4,z5,z6]),(0,[z1,z297,z886,z4,z5,z6]),(0,[z887,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z239,z5,z272]),(0,[z1,z7,z739,z4,z5,z6]),(0,[z1,z888,z3,z4,z5,z6]),(0,[z189,z421,z3,z4,z190,z6]),(0,[z889,z7,z3,z4,z5,z6]),(0,[z1,z7,z890,z4,z5,z6]),(0,[z1,z35,z7,z85,z5,z6]),(0,[z1,z204,z87,z7,z3,z18])],[(0,[z891,z7,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z828,z6]),(0,[z1,z271,z7,z4,z58,z5])],[(0,[z1,z892,z3,z4,z5,z6]),(0,[z1,z7,z14,z645,z5,z6])],[(0,[z1,z893,z3,z4,z5,z6]),(0,[z1,z204,z7,z5,z17,z18])],[(0,[z69,z3,z171,z31,z5,z6]),(0,[z1,z7,z3,z4,z894,z6]),(0,[z219,z297,z3,z171,z5,z6])],[(1,[z7,z3,z4,z722,z6])],[(0,[z1,z3,z4,z5,z6,z895]),(0,[z1,z7,z14,z660,z5,z6]),(0,[z1,z7,z3,z4,z896,z6]),(0,[z1,z7,z897,z4,z5,z6])],[(0,[z7,z739,z163,z4,z5,z6]),(0,[z89,z133,z90,z4,z5,z6]),(1,[z1,z713,z7,z5,z6]),(0,[z1,z271,z7,z27,z3,z4])]],
   [[(0,[z69,z78,z116,z4,z5,z6]),(0,[z1,z7,z3,z898,z5,z6]),(0,[z1,z3,z4,z5,z71,z207]),(0,[z333,z3,z4,z31,z5,z6]),(0,[z899,z7,z3,z4,z5,z6]),(0,[z1,z7,z900,z4,z5,z6]),(0,[z1,z70,z3,z4,z5,z772]),(0,[z1,z7,z3,z4,z5,z56]),(0,[z1,z279,z7,z3,z6,z125]),(0,[z1,z26,z7,z276,z5,z6])],[(0,[z1,z133,z3,z4,z5,z6]),(0,[z901,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z902])],[(0,[z1,z7,z903,z4,z5,z6]),(0,[z1,z7,z3,z5,z30,z709])],[(0,[z0,z11,z3,z4,z5,z6]),(0,[z1,z904,z3,z4,z5,z6]),(0,[z1,z26,z7,z58,z59,z6]),(0,[z1,z7,z3,z29,z5,z709])],[(0,[z89,z90,z4,z149,z5,z6]),(0,[z1,z905,z3,z4,z5,z6])],[(0,[z69,z1,z364,z4,z5,z6]),(1,[z1,z3,z4,z828,z6]),(0,[z1,z7,z906,z3,z5,z6])],[(0,[z0,z738,z3,z4,z5,z6]),(0,[z1,z907,z3,z4,z5,z6]),(0,[z1,z32,z3,z4,z5,z71]),(0,[z908,z7,z3,z4,z5,z6]),(0,[z1,z271,z7,z3,z4,z5]),(0,[z1,z87,z7,z4,z6,z17])],[(0,[z1,z7,z116,z179,z5,z6]),(0,[z1,z795,z4,z82,z5,z6]),(0,[z1,z462,z4,z82,z5,z6]),(0,[z1,z7,z14,z511,z5,z6])]],
   [[(0,[z1,z133,z38,z4,z5,z6]),(0,[z1,z7,z909,z3,z5,z6])],[(0,[z156,z3,z4,z5,z190,z6]),(0,[z1,z24,z7,z209,z57,z6])],[(0,[z1,z37,z3,z239,z5,z6]),(0,[z1,z7,z268,z31,z5,z6]),(0,[z52,z7,z3,z4,z841,z6]),(0,[z1,z7,z3,z4,z910,z6])],[(0,[z1,z911,z3,z4,z5,z6])],[(0,[z738,z78,z3,z4,z5,z6]),(0,[z11,z3,z4,z5,z231,z6]),(0,[z1,z7,z186,z4,z6,z497])],[(0,[z69,z3,z4,z5,z231,z6]),(0,[z1,z7,z3,z804,z5,z6]),(0,[z1,z7,z912,z4,z5,z6]),(0,[z1,z70,z3,z4,z5,z33]),(0,[z1,z913,z3,z4,z5,z6]),(0,[z1,z55,z7,z5,z6,z625]),(0,[z1,z450,z7,z3,z4,z5])],[(0,[z1,z7,z3,z5,z6,z914]),(0,[z1,z7,z3,z915,z5,z6]),(0,[z1,z7,z3,z5,z916,z6]),(0,[z1,z917,z3,z4,z5,z6])],[(0,[z69,z3,z4,z5,z249,z6]),(1,[z7,z3,z4,z5,z750]),(0,[z918,z7,z3,z4,z5,z6]),(0,[z1,z919,z3,z4,z5,z6])]],
   [[(0,[z1,z297,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z97,z51]),(0,[z1,z7,z920,z3,z5,z6]),(0,[z1,z7,z3,z4,z5,z921]),(0,[z1,z37,z795,z4,z5,z6])],[(0,[z1,z7,z3,z4,z922,z6]),(0,[z376,z7,z3,z4,z154,z6]),(0,[z1,z7,z3,z923,z5,z6]),(0,[z1,z7,z3,z4,z5,z924]),(0,[z1,z7,z4,z746,z57,z6]),(0,[z1,z7,z925,z4,z5,z6])],[(0,[z1,z7,z3,z4,z926,z6]),(0,[z1,z730,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z709,z18])],[(0,[z1,z7,z3,z29,z5,z632])],[(0,[z1,z927,z7,z3,z4,z6]),(0,[z1,z24,z7,z4,z21,z6])],[(0,[z1,z7,z3,z4,z6,z928])],[(0,[z69,z90,z4,z82,z5,z6]),(0,[z929,z7,z3,z4,z5,z6])],[(0,[z1,z930,z3,z4,z5,z6]),(0,[z247,z7,z3,z776,z5,z6]),(0,[z1,z931,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z932,z6])]],
   [[(0,[z1,z7,z116,z4,z49,z6]),(0,[z1,z933,z3,z4,z5,z6])],[(0,[z1,z7,z128,z4,z5,z6]),(0,[z1,z7,z934,z4,z5,z6]),(0,[z143,z7,z3,z4,z5,z145]),(0,[z345,z3,z4,z5,z231,z51]),(0,[z1,z2,z3,z4,z828,z6]),(0,[z1,z7,z3,z4,z6,z935]),(0,[z1,z7,z4,z5,z6,z936])],[(0,[z1,z7,z116,z4,z221,z6]),(0,[z1,z7,z4,z5,z6,z17]),(0,[z1,z204,z7,z205,z5,z18]),(0,[z45,z1,z7,z3,z4,z821])],[(0,[z1,z7,z3,z4,z937,z6]),(0,[z7,z3,z739,z4,z5,z6]),(0,[z157,z7,z3,z4,z5,z6]),(0,[z1,z109,z4,z82,z5,z6]),(0,[z1,z7,z14,z5,z567,z6]),(0,[z1,z26,z7,z276,z59,z6])],[(0,[z1,z7,z3,z938,z5,z6]),(0,[z7,z3,z776,z296,z5,z6]),(0,[z10,z7,z3,z4,z154,z6]),(0,[z376,z7,z3,z4,z5,z51]),(0,[z1,z35,z7,z4,z5,z686]),(0,[z1,z35,z279,z7,z3,z4])],[(0,[z69,z654,z3,z4,z5,z6]),(0,[z75,z7,z3,z4,z5,z51]),(0,[z32,z3,z4,z5,z71,z249])],[(0,[z1,z7,z3,z4,z5,z939]),(0,[z1,z7,z3,z4,z5,z940]),(0,[z1,z109,z12,z3,z5,z6])],[(0,[z1,z941,z3,z4,z5,z6]),(0,[z1,z496,z55,z7,z5,z6]),(0,[z942,z7,z3,z4,z5,z6])]],
   [[(0,[z7,z3,z4,z5,z145,z51]),(0,[z1,z943,z3,z4,z5,z6])],[(0,[z52,z7,z3,z4,z5,z80])],[(0,[z69,z3,z4,z172,z190,z6]),(0,[z1,z944,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z145]),(0,[z1,z421,z3,z4,z172,z6]),(0,[z1,z3,z4,z5,z6,z945])],[(0,[z1,z7,z116,z4,z5,z260]),(0,[z69,z3,z4,z346,z5,z6])],[(0,[z1,z3,z179,z31,z5,z6]),(1,[z738,z3,z4,z5,z6]),(0,[z7,z3,z4,z604,z190,z6]),(0,[z1,z156,z3,z4,z5,z33])],[(0,[z1,z168,z3,z4,z828,z6]),(0,[z1,z946,z3,z4,z5,z6]),(0,[z1,z87,z7,z3,z29,z4]),(0,[z45,z376,z7,z3,z4,z170])],[(0,[z1,z7,z947,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z948])],[(0,[z1,z7,z949,z4,z5,z6]),(0,[z143,z7,z3,z4,z114,z80])]],
   [[(0,[z1,z7,z116,z4,z5,z272]),(0,[z45,z1,z7,z3,z4,z702]),(0,[z1,z271,z7,z276,z4,z5])],[(0,[z1,z7,z3,z950,z5,z6]),(1,[z1,z7,z4,z746,z6])],[(0,[z1,z7,z116,z4,z5,z6]),(0,[z41,z7,z3,z239,z5,z6]),(0,[z1,z7,z3,z4,z951,z6]),(0,[z1,z7,z3,z4,z5,z952])],[(0,[z829,z157,z3,z4,z5,z6])],[(1,[z1,z7,z4,z5,z816]),(0,[z1,z7,z953,z4,z5,z6])],[(0,[z0,z1,z364,z4,z5,z6])],[(0,[z1,z7,z954,z4,z5,z6]),(0,[z1,z7,z3,z4,z955,z6])],[]],
   [[(0,[z1,z7,z3,z956,z5,z6]),(0,[z957,z7,z3,z4,z5,z6]),(0,[z1,z450,z7,z3,z209,z5])],[(0,[z958,z7,z3,z4,z5,z6]),(0,[z959,z7,z3,z4,z5,z6])],[(0,[z69,z78,z128,z4,z5,z6]),(0,[z7,z3,z4,z200,z5,z6]),(0,[z1,z421,z3,z4,z120,z6]),(0,[z1,z7,z3,z4,z6,z821])],[(1,[z7,z3,z776,z5,z6]),(0,[z45,z1,z7,z3,z4,z259])],[(0,[z1,z19,z3,z31,z5,z6])],[(0,[z7,z3,z4,z5,z960,z6]),(0,[z1,z7,z3,z4,z961,z6]),(0,[z1,z3,z4,z962,z5,z6]),(0,[z45,z1,z7,z3,z4,z266])],[(0,[z1,z7,z3,z4,z963,z6]),(0,[z7,z90,z739,z4,z5,z6]),(0,[z1,z7,z3,z4,z190,z145]),(0,[z7,z3,z4,z964,z5,z6])],[(0,[z333,z7,z128,z4,z5,z6]),(0,[z0,z3,z4,z5,z249,z6]),(0,[z965,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z966,z4,z5,z6]),(0,[z69,z257,z3,z4,z5,z6]),(0,[z813,z3,z4,z253,z5,z6]),(0,[z1,z7,z3,z388,z5,z6])],[(0,[z1,z7,z128,z179,z5,z6]),(0,[z1,z7,z3,z4,z967,z6]),(0,[z219,z7,z3,z171,z5,z6]),(0,[z1,z7,z3,z4,z968,z6]),(0,[z7,z3,z4,z5,z80,z750])],[(0,[z1,z37,z116,z4,z5,z6]),(0,[z1,z7,z969,z3,z5,z6])],[(0,[z1,z7,z3,z4,z49,z6]),(0,[z1,z7,z3,z4,z5,z970]),(0,[z1,z7,z971,z3,z4,z6]),(0,[z1,z7,z3,z5,z6,z972]),(0,[z1,z7,z3,z4,z821,z170])],[(0,[z1,z7,z3,z4,z973,z6]),(0,[z1,z7,z3,z4,z747,z6]),(0,[z1,z7,z276,z4,z5,z60])],[(0,[z261,z7,z3,z4,z5,z51]),(0,[z1,z109,z19,z3,z5,z6]),(0,[z168,z3,z4,z172,z200,z6]),(0,[z3,z4,z974,z253,z5,z6]),(0,[z7,z3,z4,z975,z5,z6])],[],[(0,[z247,z7,z3,z296,z5,z6]),(0,[z1,z35,z7,z258,z4,z5])]],
   [[(0,[z1,z7,z3,z4,z976,z6]),(0,[z1,z7,z977,z4,z5,z6])],[(0,[z1,z7,z3,z4,z978,z6]),(0,[z1,z7,z3,z4,z5,z979]),(0,[z1,z3,z4,z980,z5,z6]),(0,[z1,z37,z38,z244,z5,z6])],[(0,[z1,z3,z4,z149,z5,z6])],[(0,[z69,z78,z3,z179,z5,z6]),(0,[z1,z981,z3,z4,z5,z6]),(0,[z1,z583,z7,z14,z5,z6])],[(0,[z7,z3,z4,z722,z190,z6]),(0,[z982,z7,z3,z4,z5,z6])],[],[(0,[z1,z7,z3,z4,z5,z260]),(0,[z1,z7,z983,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z984])],[(0,[z1,z7,z3,z985,z5,z6])]],
   [[(0,[z1,z7,z3,z5,z6,z986]),(0,[z987,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z988,z5,z6]),(0,[z1,z7,z3,z5,z30,z521])],[(0,[z1,z7,z3,z4,z989,z6]),(0,[z1,z7,z19,z82,z5,z6]),(0,[z990,z7,z3,z4,z5,z6]),(0,[z991,z7,z3,z4,z5,z6]),(0,[z1,z713,z7,z15,z5,z6]),(0,[z1,z992,z3,z4,z5,z6]),(0,[z1,z7,z3,z72,z747,z6])],[(0,[z1,z7,z128,z4,z49,z6]),(0,[z1,z7,z3,z4,z993,z6]),(0,[z1,z7,z3,z4,z6,z994]),(0,[z1,z995,z3,z4,z5,z6]),(0,[z1,z7,z209,z16,z5,z6]),(0,[z1,z996,z3,z4,z5,z6])],[(0,[z0,z3,z4,z346,z5,z6]),(0,[z89,z7,z90,z4,z5,z6])],[(0,[z1,z7,z128,z4,z221,z6]),(0,[z7,z3,z4,z974,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6]),(0,[z1,z997,z7,z3,z4,z5]),(0,[z1,z133,z4,z82,z5,z6]),(0,[z1,z998,z7,z3,z4,z6]),(0,[z999,z1,z3,z4,z5,z6]),(0,[z1,z35,z7,z4,z192,z130]),(0,[z1,z7,z3,z4,z5,z709]),(0,[z1,z204,z87,z7,z3,z4])],[(0,[z79,z7,z163,z4,z5,z6]),(0,[z3,z4,z5,z231,z249,z6])],[]],
   [[(0,[z10,z7,z3,z4,z49,z6]),(0,[z1,z7,z3,z4,z1000,z5])],[(0,[z1,z7,z1001,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1002]),(0,[z1,z1003,z7,z3,z4,z5]),(0,[z1004,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z1005]),(0,[z1,z734,z3,z4,z5,z6])],[(0,[z1,z421,z3,z4,z221,z6]),(0,[z1,z3,z4,z1006,z5,z6]),(0,[z1,z3,z4,z5,z1007,z6])],[(0,[z7,z3,z171,z110,z5,z6])],[(0,[z69,z78,z3,z4,z49,z6]),(1,[z7,z739,z4,z5,z6]),(0,[z1,z1008,z3,z4,z5,z6]),(0,[z1009,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z819,z6])],[(0,[z1,z7,z128,z4,z5,z260]),(0,[z41,z7,z3,z171,z5,z6]),(0,[z1,z168,z3,z4,z172,z6]),(0,[z1,z7,z4,z5,z6,z1010]),(0,[z1,z7,z3,z1011,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1012]),(0,[z69,z78,z3,z4,z221,z6]),(0,[z7,z3,z4,z49,z190,z6]),(0,[z1,z3,z4,z1013,z5,z6]),(0,[z1,z7,z1014,z4,z5,z6]),(0,[z45,z1,z7,z3,z4,z170])],[(0,[z1,z7,z3,z4,z5,z1015]),(0,[z7,z90,z128,z4,z5,z6]),(0,[z69,z3,z4,z5,z71,z51]),(0,[z1,z3,z4,z379,z5,z6]),(0,[z11,z3,z4,z149,z5,z6]),(0,[z376,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z91,z6]),(0,[z45,z1,z7,z337,z3,z4])]],
   [[(0,[z69,z3,z4,z149,z5,z6]),(0,[z41,z3,z4,z82,z5,z6]),(0,[z1,z7,z4,z58,z5,z6])],[(0,[z1,z3,z239,z82,z5,z6]),(0,[z143,z421,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z120,z6])],[(0,[z1,z7,z128,z4,z5,z272]),(0,[z1,z7,z1016,z3,z5,z6]),(0,[z1,z7,z3,z5,z747,z6])],[(0,[z1,z7,z3,z179,z49,z6]),(0,[z1,z7,z3,z1017,z5,z6]),(0,[z1,z7,z3,z1018,z5,z6]),(0,[z1,z54,z55,z7,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1019]),(0,[z1,z38,z795,z4,z5,z6]),(0,[z1,z7,z4,z16,z746,z6]),(0,[z1,z3,z4,z5,z1020,z6])],[(0,[z1,z7,z3,z179,z221,z6]),(0,[z1,z7,z1021,z4,z5,z6])],[(0,[z1,z1022,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z722,z6])],[(0,[z69,z78,z3,z4,z5,z260]),(0,[z1,z297,z12,z3,z5,z6]),(0,[z1,z450,z7,z186,z3,z4])]],
   [[(0,[z10,z7,z3,z4,z5,z272]),(0,[z334,z7,z3,z4,z154,z6]),(0,[z1,z7,z38,z19,z5,z6])],[(0,[z1,z690,z4,z82,z5,z6]),(0,[z1,z7,z1023,z4,z5,z6]),(0,[z706,z7,z3,z4,z190,z6]),(0,[z1,z12,z730,z3,z5,z6]),(0,[z7,z3,z4,z1024,z5,z6])],[(0,[z1,z421,z3,z4,z5,z6]),(0,[z1,z1025,z3,z4,z5,z6]),(0,[z1,z35,z7,z4,z5,z130])],[(0,[z334,z7,z3,z4,z5,z6]),(0,[z3,z4,z299,z200,z5,z6]),(0,[z1,z7,z4,z5,z746,z6])],[(0,[z69,z78,z3,z4,z5,z272]),(0,[z1,z7,z3,z4,z1026,z6]),(0,[z189,z3,z4,z299,z190,z6]),(0,[z1027,z7,z3,z4,z5,z6]),(0,[z41,z108,z3,z31,z5,z6]),(0,[z1,z7,z14,z15,z5,z6])],[(0,[z1,z1028,z7,z3,z4,z5]),(0,[z1,z1029,z3,z4,z5,z6])],[(0,[z69,z78,z3,z4,z5,z6]),(0,[z1,z7,z3,z179,z5,z260]),(0,[z1,z7,z3,z4,z5,z1030]),(0,[z1,z7,z364,z4,z5,z6]),(0,[z1,z109,z3,z31,z5,z6]),(0,[z1,z7,z1031,z4,z5,z6])],[(0,[z1,z7,z1032,z3,z5,z6]),(0,[z7,z3,z4,z1033,z5,z6]),(0,[z7,z3,z4,z5,z1034,z6]),(0,[z1,z7,z14,z83,z5,z6]),(0,[z1,z35,z7,z4,z5,z816])]],
   [[(0,[z1,z713,z7,z4,z5,z6]),(0,[z1,z1035,z7,z3,z4,z6]),(0,[z1,z54,z713,z7,z5,z6])],[(0,[z1,z7,z3,z1036,z5,z6]),(0,[z1,z7,z1037,z4,z5,z6]),(0,[z1,z7,z3,z29,z5,z30])],[(0,[z1,z7,z1038,z4,z5,z6]),(0,[z7,z3,z776,z4,z5,z6]),(0,[z7,z3,z4,z114,z190,z6])],[(0,[z333,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z179,z5,z272]),(0,[z376,z7,z3,z4,z190,z6]),(0,[z334,z168,z3,z4,z172,z6])],[(0,[z11,z7,z3,z4,z91,z6]),(0,[z1,z1039,z7,z3,z4,z5]),(0,[z1,z7,z1040,z4,z5,z6]),(0,[z1,z7,z85,z5,z84,z6])],[(0,[z1,z7,z3,z179,z5,z6]),(0,[z69,z7,z3,z4,z91,z6]),(0,[z1,z7,z3,z4,z5,z1041])],[(0,[z1,z204,z7,z3,z5,z686])],[(0,[z345,z7,z3,z4,z5,z51])]],
   [[(0,[z1,z7,z14,z489,z5,z6])],[(0,[z69,z3,z4,z200,z5,z6]),(0,[z1,z7,z3,z1042,z5,z6]),(0,[z1,z7,z3,z4,z5,z1043])],[(0,[z41,z7,z3,z296,z5,z6])],[(0,[z1,z133,z798,z3,z5,z6]),(0,[z1,z7,z1044,z4,z5,z6]),(0,[z10,z7,z3,z4,z722,z6]),(0,[z1,z7,z268,z4,z5,z6])],[(1,[z1,z730,z3,z5,z6]),(0,[z1,z54,z533,z7,z5,z6]),(0,[z1,z7,z4,z1045,z5,z6]),(0,[z1,z7,z3,z5,z6,z1046])],[(0,[z7,z3,z4,z5,z260,z51]),(0,[z1,z1047,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1048]),(0,[z1,z7,z3,z4,z6,z192])],[(0,[z1,z7,z3,z4,z1049,z6]),(0,[z1,z7,z3,z4,z1050,z6])],[(0,[z143,z7,z3,z4,z221,z6]),(0,[z1,z7,z3,z4,z49,z260]),(0,[z1,z7,z886,z4,z5,z6]),(0,[z1,z532,z3,z4,z5,z71]),(0,[z1,z7,z3,z1051,z5,z6]),(0,[z1,z55,z713,z7,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z1052])],[(0,[z1,z7,z3,z4,z221,z260]),(0,[z1,z2,z3,z4,z221,z6]),(0,[z1,z24,z7,z388,z57,z6])],[(0,[z1,z3,z4,z5,z71,z272]),(0,[z1,z1053,z7,z4,z5,z6]),(0,[z1,z1054,z7,z3,z4,z5])],[(0,[z1,z7,z3,z209,z5,z56])],[(0,[z1,z7,z3,z4,z49,z272]),(0,[z52,z32,z3,z4,z5,z71]),(0,[z1,z7,z186,z4,z16,z6]),(0,[z1,z7,z4,z5,z84,z816])],[(0,[z1,z7,z1055,z3,z5,z6])],[(0,[z1,z7,z3,z4,z221,z272])],[(0,[z1,z7,z3,z1056,z5,z6]),(0,[z1,z3,z4,z1057,z5,z6]),(0,[z1,z7,z3,z5,z6,z125])]],
   [[(0,[z1,z7,z3,z4,z221,z6]),(0,[z52,z7,z3,z4,z5,z6]),(0,[z143,z7,z3,z4,z5,z260]),(0,[z1058,z7,z3,z4,z5,z6]),(0,[z1,z7,z36,z4,z5,z816]),(0,[z1,z7,z3,z4,z5,z60])],[(0,[z1059,z7,z3,z4,z5,z6]),(0,[z1060,z7,z3,z4,z5,z6]),(0,[z1,z7,z14,z523,z5,z6])],[(0,[z1,z7,z1061,z4,z5,z6])],[(0,[z1,z7,z3,z1062,z5,z6]),(0,[z1,z55,z7,z5,z94,z6]),(0,[z45,z1,z318,z7,z3,z4])],[(0,[z1,z116,z4,z82,z5,z6]),(0,[z1,z1063,z3,z4,z5,z6]),(0,[z1064,z7,z3,z4,z5,z6]),(0,[z1,z204,z7,z3,z5,z18])],[(0,[z1,z7,z3,z4,z5,z1065]),(0,[z1,z7,z3,z4,z5,z1066]),(0,[z1,z7,z3,z4,z5,z772]),(0,[z1,z7,z3,z4,z1067,z6])],[(0,[z1,z1068,z7,z3,z4,z6]),(0,[z1,z1069,z3,z4,z5,z6]),(0,[z1,z7,z14,z191,z5,z6])],[(0,[z1,z1070,z3,z4,z5,z6]),(0,[z1,z7,z1071,z3,z5,z6])]],
   [[(0,[z52,z7,z3,z4,z5,z51]),(0,[z1,z3,z4,z172,z828,z6]),(0,[z45,z1,z7,z3,z4,z440])],[],[(0,[z1072,z7,z3,z4,z5,z6]),(0,[z1,z24,z7,z258,z4,z6]),(0,[z1,z26,z7,z3,z747,z6])],[(0,[z1,z204,z7,z3,z42,z5])],[(0,[z1,z14,z82,z31,z5,z6]),(0,[z108,z3,z346,z31,z5,z6]),(0,[z1,z26,z7,z3,z42,z6])],[(0,[z1,z612,z7,z14,z5,z6]),(0,[z45,z1,z277,z7,z3,z4])],[(0,[z1,z7,z3,z4,z5,z272]),(0,[z1,z7,z3,z4,z6,z1073]),(0,[z1,z7,z4,z5,z6,z1074]),(0,[z1,z465,z4,z82,z5,z6]),(0,[z1,z32,z3,z4,z5,z772]),(0,[z1,z54,z7,z5,z349,z6]),(0,[z1,z24,z7,z4,z57,z6]),(0,[z1,z7,z1075,z3,z5,z6])],[(0,[z1,z7,z3,z4,z114,z6]),(0,[z1,z156,z3,z4,z5,z71]),(0,[z1,z7,z730,z3,z5,z6]),(0,[z1,z7,z1076,z4,z5,z6]),(0,[z1,z7,z1077,z4,z5,z6]),(0,[z1,z54,z7,z5,z6,z515])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 550) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 550).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1065)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [550, 515] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 158).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 158).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [158, 98] = true :=
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

end PEqualNP.Outside.L_meta_41024

theorem PEqualNP.Outside.L_meta_41024 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4274044928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4274044928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41024.solve