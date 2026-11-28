import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38291

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
  Nat.testBit (4008241888 * 2 ^ 32 + 3974144160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000c5c1b84788554#64 ++ 0x00031706e11e2155#64 ++ 0xbd1cfc7f8cf88fff#64 ++ 0xef473f1fe33e23ff#64 : BitVec 256),
   (0x40612db8b11bb330#64 ++ 0x10184b6e2c46eccc#64 ++ 0xfee33fb8f33ff332#64 ++ 0xbfb8cfee3ccffccc#64 : BitVec 256),
   (0x8f0282c05b805aa8#64 ++ 0x23c0a0b016e016aa#64 ++ 0xdf03c3c0ffc0ffff#64 ++ 0xf7c0f0f03ff03fff#64 : BitVec 256),
   (0x23b403ed03ed03c1#64 ++ 0x08ed00fb40fb40f0#64 ++ 0xeffc03ff03ff03c3#64 ++ 0x3bff00ffc0ffc0f0#64 : BitVec 256),
   (0x17dff40002f6ec00#64 ++ 0x85f7fd0000bdbb00#64 ++ 0xf7fffc0003fffc00#64 ++ 0x3dffff0000ffff00#64 : BitVec 256),
   (0x3bfbfb76ec000000#64 ++ 0x4efefeddbb000000#64 ++ 0xfbfffffffc000000#64 ++ 0x3effffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z1 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z2 : W := mkw 0x184bf812ec000000 0x4612fe04bb000000 0xb91ffc7ffc000000 0x2e47ff1fff000000

def z3 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z4 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfbfffffffc000000 0x3effffffff000000

def z5 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z6 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z7 : W := mkw 0x0004040900788554 0x00010102401e2155 0x0400000000f88fff 0xc1000000003e23ff

def z8 : W := mkw 0x3bffff7fec788554 0x4effffdffb1e2155 0xfffffffffcf88fff 0xffffffffff3e23ff

def z9 : W := mkw 0x3ffff7646af6ec00 0xcffffdd91abdbb00 0xf7ffff8073fffc00 0x3dffffe01cffff00

def z10 : W := mkw 0x23b003e403850281 0x08ec00f900e140a0 0xcfe003c003c703c3 0x33f800f000f1c0f0

def z11 : W := mkw 0x0702800002804800 0x01c0a00000a01200 0xd703c00003c0fc00 0x35c0f00000f03f00

def z12 : W := mkw 0x9fdff6c05bf6fea8 0xa7f7fdb016fdbfaa 0xffffffc0ffffffff 0xfffffff03fffffff

def z13 : W := mkw 0x8400008013805aa8 0x2100002004e016aa 0x0400000003c0ffff 0xc100000000f03fff

def z14 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xffffc3ffffffffff 0xfffff0ffffffffff

def z15 : W := mkw 0x20b0012400000000 0x082c004900000000 0x20fc003f00000000 0x083f000fc0000000

def z16 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0x20fc003f003f0000 0x083f000fc00fc000

def z17 : W := mkw 0x3b9ad2464c000000 0x4ee6b49193000000 0x011cc0470c000000 0x00473011c3000000

def z18 : W := mkw 0x40000488111bb330 0x100001220446eccc 0x04000000033ff332 0x8100000000cffccc

def z19 : W := mkw 0x004124000012a000 0x001049000004a800 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z20 : W := mkw 0x406d7dbbb57bb774 0x101b5f6eed5eeddd 0xffffffffffffffff 0xffffffffffffffff

def z21 : W := mkw 0x28200b76ec000000 0x4a0802ddbb000000 0x080003fffc000000 0x020000ffff000000

def z22 : W := mkw 0x40412c10b012b030 0x10104b042c04ac0c 0x10033c00f000f030 0x8400cf003c003c0c

def z23 : W := mkw 0x63f52ffdb3ffb3f1 0x18fd4bff6cffecfc 0xffff3ffff3fff3f3 0xbfffcffffcfffcfc

def z24 : W := mkw 0x3bbed3ef4fed03c1 0x4eefb4fbd3fb40f0 0xeffcc3ff0fff03c3 0x3bff30ffc3ffc0f0

def z25 : W := mkw 0x23b003e403850281 0x08ec00f900e140a0 0x42e0038003070000 0x10b800e000c1c000

def z26 : W := mkw 0x3bf3a36468000000 0x4efce8d91a000000 0x42e3038070000000 0x10b8c0e01c000000

def z27 : W := mkw 0xbffbfbf6ff805aa8 0x6ffefefdbfe016aa 0xffffffffffc0ffff 0xfffffffffff03fff

def z28 : W := mkw 0x144bf4000012ec00 0x8512fd000004bb00 0x1003fc000000fc00 0x0400ff0000003f00

def z29 : W := mkw 0x0000081b84080154 0x00000206e1020055 0x0800007f8c0003ff 0xc200001fe30000ff

def z30 : W := mkw 0x880002c0590012a8 0x220000b0164004aa 0x0000038070000000 0x000000e01c000000

def z31 : W := mkw 0x0004000900680140 0x00010002401a0050 0xad1c007f00f803c3 0x2b47001fc03e00f0

def z32 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x4203038073007000 0x1080c0e01cc01c00

def z33 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0x080003b8f0000332 0x820000ee3c0000cc

def z34 : W := mkw 0x2bb00b76ec000000 0x4aec02ddbb000000 0xebfc03fffc000000 0x3aff00ffff000000

def z35 : W := mkw 0x2394024502e400c1 0x08e5009140b90030 0xe7fc004703ff00c1 0x39ff0011c0ffc030

def z36 : W := mkw 0x00612930a0000000 0x00184a4c28000000 0xfae33fb8f0000000 0x3eb8cfee3c000000

def z37 : W := mkw 0x0000008001000200 0x0000002000400080 0xce00038003000302 0x338000e000c000c0

def z38 : W := mkw 0x8f2283e85b895ba8 0x23c8a0fa16e256ea 0xffe3c3f8ffffffff 0xfff8f0fe3fffffff

def z39 : W := mkw 0x3bbad3664c000000 0x4eeeb4d993000000 0xebfcc3ff0c000000 0x3aff30ffc3000000

def z40 : W := mkw 0x13dbf4000012a000 0x04f6fd000004a800 0xf7fffc00033ff000 0x3dffff0000cffc00

def z41 : W := mkw 0x17dffc1286f6ec00 0x85f7ff04a1bdbb00 0xfffffc7f8ffffc00 0x3fffff1fe3ffff00

def z42 : W := mkw 0x63f523ed33ef33e1 0x18fd48fb4cfbccf8 0xefff03ff73ff73c3 0x3bffc0ffdcffdcf0

def z43 : W := mkw 0x0394000002e40000 0x00e5000000b90000 0xe7fc000003ff0000 0x39ff000000ffc000

def z44 : W := mkw 0x10d9700000000000 0x04365c0000000000 0x20fc3c0000000000 0x083f0f0000000000

def z45 : W := mkw 0x57fffdb8b3ffff30 0x95ffff6e2cffffcc 0xffffffb8f3ffff32 0xbfffffee3cffffcc

def z46 : W := mkw 0x7bfbfffefd1bb330 0x5efeffffbf46eccc 0xffffffffff3ff332 0xbfffffffffcffccc

def z47 : W := mkw 0x57dff48813ffff30 0x95f7fd2204ffffcc 0xf7fffc0003ffff32 0xbdffff0000ffffcc

def z48 : W := mkw 0x840c5c9b97f8dffc 0x21031726e5fe37ff 0xbd1cfc7f8ff8ffff 0xef473f1fe3fe3fff

def z49 : W := mkw 0x17d3a00002866800 0x85f4e80000a19a00 0x42e3000003077000 0x10b8c00000c1dc00

def z50 : W := mkw 0x406125a03113b220 0x101849680c44ec88 0xf6e33f80733ff000 0x3db8cfe01ccffc00

def z51 : W := mkw 0x4000008011033220 0x100000200440cc88 0x0000000003077000 0x0000000000c1dc00

def z52 : W := mkw 0x0008581284000000 0x00021604a1000000 0xb91cfc7f8c000000 0x2e473f1fe3000000

def z53 : W := mkw 0x8c0280805b805aa8 0x2300a02016e016aa 0x1403c000ffc0ffff 0xc500f0003ff03fff

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z55 : W := mkw 0x000c540000708400 0x00031500001c2100 0xb51cfc0000f88c00 0x2d473f00003e2300

def z56 : W := mkw 0x144bfc128412ec14 0x8512ff04a104bb05 0x1003fc008c00fc3c 0xc400ff0023003f0f

def z57 : W := mkw 0x00697932a4000000 0x001a5e4ca9000000 0xfbfffffffc000000 0x3effffffff000000

def z58 : W := mkw 0x0000000000000000 0x0000000000000000 0x9d00c0408cc08fff 0xe7403010233023ff

def z59 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0x62ff3fbf70000000 0x18bfcfefdc000000

def z60 : W := mkw 0x202c5fff857987d5 0x080b17ffe15e61f5 0xbd1cffff8cf88fff 0xef473fffe33e23ff

def z61 : W := mkw 0x0400000002804800 0x0100000000a01200 0x0400000003c0fc00 0x0100000000f03f00

def z62 : W := mkw 0xcf228bf8fb895bb8 0x33c8a2fe3ee256ee 0xdf03c3f8ffc0ffff 0xf7c0f0fe3ff03fff

def z63 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0xde0303b8f300f332 0xb780c0ee3cc03ccc

def z64 : W := mkw 0x8400000010005828 0x210000000400160a 0x000000000000fc3c 0xc000000000003f0f

def z65 : W := mkw 0x00040c1980788554 0x00010306601e2155 0xbc003c3880f88fff 0xef000f0e203e23ff

def z66 : W := mkw 0x0b02824048000000 0x02c0a09012000000 0xdb03c3c0fc000000 0x36c0f0f03f000000

def z67 : W := mkw 0x23b4036d00680140 0x08ed00db401a0050 0xeffc03ff00f803c3 0x3bff00ffc03e00f0

def z68 : W := mkw 0x000c5c1284708414 0x00031704a11c2105 0xb51cfc008cf88c3c 0xed473f00233e230f

def z69 : W := mkw 0x202003ed010903c1 0x080800fb404240f0 0x080003ff000003c3 0x020000ffc00000f0

def z70 : W := mkw 0x8f0282404a804888 0x23c0a09012a01222 0x0100c0400cc00ccd 0x4040301003300333

def z71 : W := mkw 0x8400008013805aa8 0x2100002004e016aa 0x0000000003007000 0x0000000000c01c00

def z72 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0xadfc007f00ff03c3 0x2b7f001fc03fc0f0

def z73 : W := mkw 0x37fff7ed03ffefc1 0x8dfffdfb40fffbf0 0xffffffff03ffffc3 0x3fffffffc0fffff0

def z74 : W := mkw 0x0000008011001220 0x0000002004400488 0xde030380f300f332 0xb780c0e03cc03ccc

def z75 : W := mkw 0x3b9ede5fcc788554 0x4ee7b797f31e2155 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z76 : W := mkw 0x30f97936a4000000 0x4c3e5e4da9000000 0xfaff3fbff0000000 0x3ebfcfeffc000000

def z77 : W := mkw 0x20b401ad016d0341 0x082d006b405b40d0 0xeefc03bf033f0302 0x3bbf00efc0cfc0c0

def z78 : W := mkw 0x0004008903ed03c1 0x0001002240fb40f0 0x0400000003ff03c3 0x0100000000ffc0f0

def z79 : W := mkw 0x184bf812ec000000 0x4612fe04bb000000 0x1003fc00fc000000 0x0400ff003f000000

def z80 : W := mkw 0x9fdff6404af6ec88 0xa7f7fd9012bdbb22 0xf7fffc400ffffccd 0x7dffff1003ffff33

def z81 : W := mkw 0x1792800002844800 0x85e4a00000a11200 0x0000000000000000 0x0000000000000000

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0xd60300000300f000 0x3580c00000c03c00

def z83 : W := mkw 0x1843a00068000000 0x4610e8001a000000 0x0003000070000000 0x0000c0001c000000

def z84 : W := mkw 0x00085c1284108414 0x00021704a1042105 0x1000fc008c008c3c 0xc4003f002300230f

def z85 : W := mkw 0xbffffff6fff6fea8 0xeffffffdbffdbfaa 0xffffffffffffffff 0xffffffffffffffff

def z86 : W := mkw 0x27b683ed03ed4bc1 0x09eda0fb40fb52f0 0xffffc3ff03ffffc3 0x3ffff0ffc0fffff0

def z87 : W := mkw 0x144bf4000012ec00 0x8512fd000004bb00 0xf6e3fc00033ffc00 0x3db8ff0000cfff00

def z88 : W := mkw 0x40697dbab51bb330 0x101a5f6ead46eccc 0xffffffffff3ff332 0xbfffffffffcffccc

def z89 : W := mkw 0x13dff40000708400 0x04f7fd00001c2100 0xf7fffc0000f88c00 0x3dffff00003e2300

def z90 : W := mkw 0x0702808013805a20 0x01c0a02004e01688 0xdf03c380f3c0ff32 0xb7c0f0e03cf03fcc

def z91 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x281c3c7f8c3803ff 0xca070f1fe30e00ff

def z92 : W := mkw 0x23b4012d02ed0141 0x08ed004b40bb4050 0xe7fc003f03ff0000 0x39ff000fc0ffc000

def z93 : W := mkw 0x0000008003800280 0x0000002000e000a0 0x0400000003c003c3 0x0100000000f000f0

def z94 : W := mkw 0x23b003e403850281 0x08ec00f900e140a0 0xebfc03ff03070000 0x3aff00ffc0c1c000

def z95 : W := mkw 0x00000c1880188110 0x0000030620062044 0xbc003c3880388332 0xaf000f0e200e20cc

def z96 : W := mkw 0x000c500304600444 0x00031400c1180111 0x011cc0470cc00ccd 0x40473011c3300333

def z97 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfffffffffcc08fff 0xffffffffff3023ff

def z98 : W := mkw 0x3f9ed2464ee44c00 0xcfe7b49193b91300 0x011cc0470cc00c00 0x00473011c3300300

def z99 : W := mkw 0x8f0ededbdff8dffc 0x23c3b7b6f7fe37ff 0xff1ffffffff8ffff 0xffc7fffffffe3fff

def z100 : W := mkw 0x179ed00002e44c00 0x85e7b40000b91300 0x011cc00000c00c00 0x0047300000300300

def z101 : W := mkw 0x8c02800058005828 0x2300a0001600160a 0x1003c000fc00fc3c 0xc400f0003f003f0f

def z102 : W := mkw 0x23b003ed010903c1 0x08ec00fb404240f0 0xebfc03ff000003c3 0x3aff00ffc00000f0

def z103 : W := mkw 0x144ff40002f6ec00 0x8513fd0000bdbb00 0x1403fc0003fffc00 0x0500ff0000ffff00

def z104 : W := mkw 0x002001a801090300 0x0008006a004240c0 0xeee003b8033f0302 0x3bb800ee00cfc0c0

def z105 : W := mkw 0x40612d38a01ba110 0x10184b4e2806e844 0x20e03c38003f0000 0x08380f0e000fc000

def z106 : W := mkw 0x3bf3ab74e8000000 0x4efceadd3a000000 0xfae33fb8f0000000 0x3eb8cfee3c000000

def z107 : W := mkw 0x202403ed03ed03c1 0x080900fb40fb40f0 0x0c0003ff03ff03c3 0x030000ffc0ffc0f0

def z108 : W := mkw 0x38f97b76ec000000 0x4e3e5eddbb000000 0x28fc3ffffc000000 0x0a3f0fffff000000

def z109 : W := mkw 0x9c4bf4005812fc28 0xa712fd001604bf0a 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z110 : W := mkw 0x8f63abf0fb805aa8 0x23d8eafc3ee016aa 0xffe3fff8ffc0ffff 0xfff8fffe3ff03fff

def z111 : W := mkw 0x1fdff6404af6ec00 0x87f7fd9012bdbb00 0xffffffc0fffffc00 0x3ffffff03fffff00

def z112 : W := mkw 0x3bfbf36468000000 0x4efefcd91a000000 0xf3ffff8070000000 0x3cffffe01c000000

def z113 : W := mkw 0x006125a8011ba300 0x0018496a0046e8c0 0xfee33fb8033ff302 0x3fb8cfee00cffcc0

def z114 : W := mkw 0x1fdffc12eef6ec00 0xc7f7ff04bbbdbb00 0xf7fffc00fffffc00 0x3dffff003fffff00

def z115 : W := mkw 0x0000081284000000 0x00000204a1000000 0x0800007f8c000000 0x0200001fe3000000

def z116 : W := mkw 0x2020036400000000 0x080800d900000000 0x080003ff00000000 0x020000ffc0000000

def z117 : W := mkw 0x3bfffbffefed03c1 0x4efffefffbfb40f0 0xffffffffffff03c3 0x3fffffffffffc0f0

def z118 : W := mkw 0x3bf3ab76ec000000 0x4efceaddbb000000 0x4ae303fffc000000 0x12b8c0ffff000000

def z119 : W := mkw 0x03b401a803ed0300 0x00ed006a00fb40c0 0xeffc03b803ff0302 0x3bff00ee00ffc0c0

def z120 : W := mkw 0x10dd74000076a400 0x84375d00001da900 0x20fc3c00003f0000 0x083f0f00000fc000

def z121 : W := mkw 0x880002c0590012a8 0x220000b0164004aa 0x080003c0fc0003ff 0xc20000f03f0000ff

def z122 : W := mkw 0xeff7affdfbfffbf9 0x3bfdebff7efffefe 0xffffffffffffffff 0xffffffffffffffff

def z123 : W := mkw 0xafb683ed4bed4bc9 0x2beda0fb52fb52f2 0xeffcc3ff0fff0fcf 0x7bff30ffc3ffc3f3

def z124 : W := mkw 0x3bfbfbf6ef850281 0x4efefefdbbe140a0 0xfbffffffff070000 0x3effffffffc1c000

def z125 : W := mkw 0x40652db9b17bb774 0x10194b6e6c5eeddd 0xfee33fb8f3ffffff 0xffb8cfee3cffffff

def z126 : W := mkw 0x3bfbf3666c000000 0x4efefcd99b000000 0x43ffc3c77c000000 0x10fff0f1df000000

def z127 : W := mkw 0x3fffff76eef6ec00 0xcfffffddbbbdbb00 0xfffffffffffffc00 0x3fffffffffffff00

def z128 : W := mkw 0x23b0036400000000 0x08ec00d900000000 0xebfc03ff00000000 0x3aff00ffc0000000

def z129 : W := mkw 0x20bc5d3f847d8555 0x082f174fe11f6155 0xbdfcfc7f8cff8fff 0xef7f3f1fe33fe3ff

def z130 : W := mkw 0x17dff40902feed54 0x85f7fd0240bfbb55 0xf7fffc0003ffffff 0xfdffff0000ffffff

def z131 : W := mkw 0x406121a031033220 0x101848680c40cc88 0x42e3038073077000 0x10b8c0e01cc1dc00

def z132 : W := mkw 0x0794040002f6ec00 0x81e5010000bdbb00 0xe7fc000003fffc00 0x39ff000000ffff00

def z133 : W := mkw 0x584bfc12fc12b030 0x5612ff04bf04ac0c 0x1003fc00fc00f030 0x8400ff003f003c0c

def z134 : W := mkw 0x00612d30a012a000 0x00184b4c2804a800 0xfee33fb8f33ff000 0x3fb8cfee3ccffc00

def z135 : W := mkw 0x1bdbf24048000000 0x06f6fc9012000000 0xfbffffc0fc000000 0x3efffff03f000000

def z136 : W := mkw 0xbffffbffffed5be9 0x6ffffefffffb56fa 0xffffffffffffffff 0xffffffffffffffff

def z137 : W := mkw 0x17dffc1b86feed54 0x85f7ff06e1bfbb55 0xfffffc7f8fffffff 0xffffff1fe3ffffff

def z138 : W := mkw 0x186bf932ec000000 0x461afe4cbb000000 0xfae3ffb8fc000000 0x3eb8ffee3f000000

def z139 : W := mkw 0x10dd7c1b847ea554 0x84375f06e11fa955 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z140 : W := mkw 0xcf63aff8fb9bfbb8 0x33d8ebfe3ee6feee 0xffe3fff8ffffffff 0xfff8fffe3fffffff

def z141 : W := mkw 0x8404048913f8dffc 0x2101012244fe37ff 0x0400000003f8ffff 0xc100000000fe3fff

def z142 : W := mkw 0x000c5c1880788510 0x00031706201e2144 0xbd1cfc3880f88f32 0xaf473f0e203e23cc

def z143 : W := mkw 0xcf0286c85b9bfbb8 0x33c0a1b216e6feee 0xdf03c3c0ffffffff 0xf7c0f0f03fffffff

def z144 : W := mkw 0xcf63a3e07b837aa8 0x33d8e8f81ee0deaa 0x42e3038073077000 0x10b8c0e01cc1dc00

def z145 : W := mkw 0x8c0adc12dc10dc3c 0x2302b704b704370f 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z146 : W := mkw 0x23b403ed13ed13e1 0x08ed00fb44fb44f8 0xffff03fff3fff3f3 0xbfffc0fffcfffcfc

def z147 : W := mkw 0xabb403ed5bed13e9 0x2aed00fb56fb44fa 0xeffc03ffffff03ff 0xfbff00ffffffc0ff

def z148 : W := mkw 0x17dff48013f6fe20 0x85f7fd2004fdbf88 0xffffff80f3ffff32 0xbfffffe03cffffcc

def z149 : W := mkw 0x004d74000072a400 0x00135d00001ca900 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z150 : W := mkw 0x004124000012a000 0x001049000004a800 0x10033c000000f000 0x0400cf0000003c00

def z151 : W := mkw 0x00040009006d0141 0x00010002401b4050 0x00000000003f0000 0x00000000000fc000

def z152 : W := mkw 0x8f43a6c05b92faa8 0x23d0e9b016e4beaa 0xffe3ffc0ffffffff 0xfff8fff03fffffff

def z153 : W := mkw 0x000c540000708400 0x00031500001c2100 0xbd1cfc408cf88fff 0xef473f10233e23ff

def z154 : W := mkw 0x9f9ed2404ae44c88 0xa7e7b49012b91322 0x011cc0400cc00ccd 0x4047301003300333

def z155 : W := mkw 0x030002c003800280 0x00c000b000e000a0 0xcf0003c003c003c3 0x33c000f000f000f0

def z156 : W := mkw 0xbf9ad2c65f805aa8 0x6fe6b4b197e016aa 0xdf1fc3c7ffc0ffff 0xf7c7f0f1fff03fff

def z157 : W := mkw 0x00000c1080108010 0x0000030420042004 0x10003c0080008030 0x84000f002000200c

def z158 : W := mkw 0x002401a901690340 0x0009006a405a40d0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z159 : W := mkw 0x000c581b84680554 0x00031606e11a0155 0x091cc07f8cc00fff 0xc247301fe33003ff

def z160 : W := mkw 0x10dd7c1b847ea554 0x84375f06e11fa955 0xbdfcfc7f8cff8fff 0xef7f3f1fe33fe3ff

def z161 : W := mkw 0x2394024502e400c1 0x08e5009140b90030 0x011c004700c000c1 0x00470011c0300030

def z162 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xffe3fff8ffffffff 0xfff8fffe3fffffff

def z163 : W := mkw 0x002401a903ed03c1 0x0009006a40fb40f0 0xeee003b803ff03c3 0x3bb800ee00ffc0f0

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x8d00004000c003c3 0x23400010003000f0

def z165 : W := mkw 0x0008581284000000 0x00021604a1000000 0x1000fc008c000000 0x04003f0023000000

def z166 : W := mkw 0x0394000002e40000 0x00e5000000b90000 0x011c000000c00000 0x0047000000300000

def z167 : W := mkw 0x13dbf00000000000 0x04f6fc0000000000 0xf3fffc0000000000 0x3cffff0000000000

def z168 : W := mkw 0x406d7db8b17bb730 0x101b5f6e2c5eedcc 0xffffffb8f3ffff32 0xbfffffee3cffffcc

def z169 : W := mkw 0x17dffc1286f6ec14 0x85f7ff04a1bdbb05 0xf7fffc008ffffc3c 0xfdffff0023ffff0f

def z170 : W := mkw 0x184bfc12ec108414 0x4612ff04bb042105 0x1003fc00fc008c3c 0xc400ff003f00230f

def z171 : W := mkw 0x8f028ed8db98dbb8 0x23c0a3b636e636ee 0xff03fff8fff8ffff 0xffc0fffe3ffe3fff

def z172 : W := mkw 0x44652db8b3ffff30 0x91194b6e2cffffcc 0xfee33fb8f3ffff32 0xbfb8cfee3cffffcc

def z173 : W := mkw 0x30f97936a4000000 0x4c3e5e4da9000000 0x20fc3c3f00000000 0x083f0f0fc0000000

def z174 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x241c3c3f00f88fff 0xc9070f0fc03e23ff

def z175 : W := mkw 0xc8200bf8f90913b8 0x320802fe3e4244ee 0x080003f8fc0003ff 0xc20000fe3f0000ff

def z176 : W := mkw 0x40697dbab51bb734 0x101a5f6ead46edcd 0xfee3ffb8ff3fff3e 0xffb8ffee3fcfffcf

def z177 : W := mkw 0x17dbf00002866800 0x85f6fc0000a19a00 0xf3fffc0003077000 0x3cffff0000c1dc00

def z178 : W := mkw 0x23b003ec038d0381 0x08ec00fb00e340e0 0xeee003b8033f0302 0x3bb800ee00cfc0c0

def z179 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0x091c03ff00c003c3 0x024700ffc03000f0

def z180 : W := mkw 0xbffbfb76ee804888 0x6ffefeddbba01222 0xfbfffffffcc00ccd 0x7effffffff300333

def z181 : W := mkw 0x17dff40306f6ec44 0x85f7fd00c1bdbb11 0xf7fffc470ffffccd 0x7dffff11c3ffff33

def z182 : W := mkw 0x7bfbff7eec1ba110 0x5efeffdfbb06e844 0xfbfffffffc3f0000 0x3effffffff0fc000

def z183 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x201c3c3f00380000 0x08070f0fc00e0000

def z184 : W := mkw 0x0041200000000000 0x0010480000000000 0xf2e33c0000000000 0x3cb8cf0000000000

def z185 : W := mkw 0x3bf3a3e46b850281 0x4efce8f91ae140a0 0x42e3038073070000 0x10b8c0e01cc1c000

def z186 : W := mkw 0x0094000000640000 0x0025000000190000 0x20fc0000003f0000 0x083f0000000fc000

def z187 : W := mkw 0x0702800002804800 0x01c0a00000a01200 0x0100c00000c00c00 0x0040300000300300

def z188 : W := mkw 0x10497812a4000000 0x44125e04a9000000 0x00003c0000000000 0x00000f0000000000

def z189 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0x111ffc0000c0fc00 0x0447ff0000303f00

def z190 : W := mkw 0x0004000900680140 0x00010002401a0050 0xbd1cc07f8cf88fff 0xef47301fe33e23ff

def z191 : W := mkw 0x10dd74000076a400 0x84375d00001da900 0xf6ff3c00033ff000 0x3dbfcf0000cffc00

def z192 : W := mkw 0xbffbfbf6ff805aa8 0x6ffefefdbfe016aa 0xfbffffffff007000 0x3effffffffc01c00

def z193 : W := mkw 0x8f0280005a805828 0x23c0a00016a0160a 0xd703c000ffc0fc3c 0xf5c0f0003ff03f0f

def z194 : W := mkw 0x002001a801090300 0x0008006a004240c0 0x080003b800000302 0x020000ee000000c0

def z195 : W := mkw 0x870002c013805aa8 0x21c000b004e016aa 0xcf0003c003c0ffff 0xf3c000f000f03fff

def z196 : W := mkw 0x37dff64502f6ecc1 0x8df7fd9140bdbb30 0xf7fffc4703fffcc1 0x3dffff11c0ffff30

def z197 : W := mkw 0xa82003ed590913e9 0x2a0800fb564244fa 0x080003fffc0003ff 0xc20000ffff0000ff

def z198 : W := mkw 0x17fffd30a2f6ec00 0x85ffff4c28bdbb00 0xffffffb8f3fffc00 0x3fffffee3cffff00

def z199 : W := mkw 0x23b003ec01090300 0x08ec00fb004240c0 0xeffc03ff033f0302 0x3bff00ffc0cfc0c0

def z200 : W := mkw 0x000c540000708400 0x00031500001c2100 0x201c3c0000380000 0x08070f00000e0000

def z201 : W := mkw 0x0004000100600444 0x0001000040180111 0x0000000000c00ccd 0x4000000000300333

def z202 : W := mkw 0x070ed40002f0cc00 0x01c3b50000bc3300 0xf71ffc0003f8fc00 0x3dc7ff0000fe3f00

def z203 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0x28e03fb8f03f0332 0x8a380fee3c0fc0cc

def z204 : W := mkw 0x3bfffb77eee400c1 0x4efffeddfbb90030 0xfbfffffffcc000c1 0x3effffffff300030

def z205 : W := mkw 0x239c524706e404c5 0x08e71491c1b90131 0x011cc0470cc00ccd 0x40473011c3300333

def z206 : W := mkw 0x40412c98b11bb330 0x10104b262c46eccc 0x14033c00f33ff332 0x8500cf003ccffccc

def z207 : W := mkw 0x586bfdbafd1bb330 0x561aff6ebf46eccc 0xfee3ffb8ff3ff332 0xbfb8ffee3fcffccc

def z208 : W := mkw 0x40000408001ba110 0x100001020006e844 0x00000000003f0000 0x00000000000fc000

def z209 : W := mkw 0x20b401ad03ed03c1 0x082d006b40fb40f0 0x24fc003f03ff03c3 0x093f000fc0ffc0f0

def z210 : W := mkw 0x0404040002f6ec00 0x8101010000bdbb00 0x0400000003fffc00 0x0100000000ffff00

def z211 : W := mkw 0x8c0282c059005aa8 0x2300a0b0164016aa 0x1803c3c0fc00ffff 0xc600f0f03f003fff

def z212 : W := mkw 0x00000c1b84188154 0x00000306e1062055 0xbc003c7f8c3883ff 0xef000f1fe30e20ff

def z213 : W := mkw 0x3ffffb76eee44c00 0xcffffeddbbb91300 0xfbfffffffcc00c00 0x3effffffff300300

def z214 : W := mkw 0x2bb2836448000000 0x0aeca0d912000000 0xfbffc3fffc000000 0x3efff0ffff000000

def z215 : W := mkw 0x0404040902feed54 0x8101010240bfbb55 0x0400000003ffffff 0xc100000000ffffff

def z216 : W := mkw 0x0004000900680140 0x00010002401a0050 0x201c003f00380000 0x0807000fc00e0000

def z217 : W := mkw 0x3bf3a36468000000 0x4efce8d91a000000 0xebff03ff70000000 0x3affc0ffdc000000

def z218 : W := mkw 0x144ff4000072ec00 0x8513fd00001cbb00 0xb51ffc0000f8fc00 0x2d47ff00003e3f00

def z219 : W := mkw 0x0000040800188110 0x0000010200062044 0x0400000000388332 0x81000000000e20cc

def z220 : W := mkw 0x77fffffdb3fffff1 0x9dffffff6cfffffc 0xfffffffff3fffff3 0xbffffffffcfffffc

def z221 : W := mkw 0x63b407ed13ffb3f1 0x18ed01fb44ffecfc 0xeffc03ff03fff3f3 0xbbff00ffc0fffcfc

def z222 : W := mkw 0x2bb683ed4bed03c1 0x0aeda0fb52fb40f0 0xffffc3ffffff03c3 0x3ffff0ffffffc0f0

def z223 : W := mkw 0x0702800002804800 0x01c0a00000a01200 0x4203000003007000 0x1080c00000c01c00

def z224 : W := mkw 0x17dff00002e66c00 0x85f7fc0000b99b00 0x43ffc00003c77c00 0x10fff00000f1df00

def z225 : W := mkw 0x23b40bff87ed03d5 0x08ed02ffe1fb40f5 0xeffc03ff8fff03ff 0xfbff00ffe3ffc0ff

def z226 : W := mkw 0x38fbf936ec000000 0x4e3efe4dbb000000 0x30fffc3ffc000000 0x0c3fff0fff000000

def z227 : W := mkw 0x23b4036d02ed01c1 0x08ed00db40bb4070 0x21fc007f00ff00c1 0x087f001fc03fc030

def z228 : W := mkw 0x8f0aded2df90debc 0x23c2b7b4b7e437af 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z229 : W := mkw 0x402009bbb5091374 0x1008026eed4244dd 0x080003fffc0003ff 0xc20000ffff0000ff

def z230 : W := mkw 0x0404048903ffefc1 0x8101012240fffbf0 0x0400000003ffffc3 0x0100000000fffff0

def z231 : W := mkw 0x60f52dbdb17fb371 0x183d4b6f6c5fecdc 0xfeff3fbff33ff332 0xbfbfcfeffccffccc

def z232 : W := mkw 0xbff3a3e47b805aa8 0x6ffce8f91ee016aa 0x42e3038073007000 0x10b8c0e01cc01c00

def z233 : W := mkw 0x0b02824048000000 0x02c0a09012000000 0x4203038070000000 0x1080c0e01c000000

def z234 : W := mkw 0x2390024400000000 0x08e4009100000000 0x011c004700000000 0x00470011c0000000

def z235 : W := mkw 0x3bfbfb7fec080154 0x4efefedffb020055 0xfbfffffffc0003ff 0xfeffffffff0000ff

def z236 : W := mkw 0x20200936a4000000 0x4808024da9000000 0x0000003f00000000 0x0000000fc0000000

def z237 : W := mkw 0xbffbfb76fc005828 0x6ffefeddbf00160a 0xfbfffffffc00fc3c 0xfeffffffff003f0f

def z238 : W := mkw 0x1443a00000026800 0x8510e80000009a00 0x0003000000007000 0x0000c00000001c00

def z239 : W := mkw 0x0004048903fd87d5 0x0001012240ff61f5 0x0400000003ff8fff 0xc100000000ffe3ff

def z240 : W := mkw 0x17dffc1b86feed54 0x85f7ff06e1bfbb55 0xf7fffc3f03fffc00 0x3dffff0fc0ffff00

def z241 : W := mkw 0x040c5c1b86feed54 0x81031706e1bfbb55 0xbd1cfc7f8fffffff 0xef473f1fe3ffffff

def z242 : W := mkw 0x00085c1284108414 0x00021704a1042105 0x9d00fc408cc08fff 0xe7403f10233023ff

def z243 : W := mkw 0x000c581384600444 0x00031604e1180111 0xb91cfc7f8cc00ccd 0x6e473f1fe3300333

def z244 : W := mkw 0x4b63aff8f91bb330 0x12d8ebfe3e46eccc 0xffe3fff8ff3ff332 0xbff8fffe3fcffccc

def z245 : W := mkw 0x202003e401010281 0x080800f9004040a0 0x0000038000000000 0x000000e000000000

def z246 : W := mkw 0x23b403e503e502c1 0x08ed00f940f940b0 0x43fc03c703c700c1 0x10ff00f1c0f1c030

def z247 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xefff03ff73ff73c3 0x3bffc0ffdcffdcf0

def z248 : W := mkw 0x68612ffefd1bb330 0x5a184bffbf46eccc 0xfee33fffff3ff332 0xbfb8cfffffcffccc

def z249 : W := mkw 0x000c500000600400 0x0003140000180100 0x011cc00000c00c00 0x0047300000300300

def z250 : W := mkw 0x8404008913ed5be9 0x2101002244fb56fa 0x0400000003ffffff 0xc100000000ffffff

def z251 : W := mkw 0x3bfffb7fec6d0141 0x4efffedffb1b4050 0xfbfffffffc3f0000 0x3effffffff0fc000

def z252 : W := mkw 0x0b02824048000000 0x02c0a09012000000 0xdf03c3c0fcc08fff 0xf7c0f0f03f3023ff

def z253 : W := mkw 0x23b003e403800280 0x08ec00f900e000a0 0xeffc03ff03c003c3 0x3bff00ffc0f000f0

def z254 : W := mkw 0x3b9ada56cc000000 0x4ee6b695b3000000 0xb91cfc7f8c000000 0x2e473f1fe3000000

def z255 : W := mkw 0x1bdbf812ec000000 0x46f6fe04bb000000 0xf3fffc00fc000000 0x3cffff003f000000

def z256 : W := mkw 0x3fdff6464ef6ec00 0xcff7fd9193bdbb00 0xf7fffc470ffffc00 0x3dffff11c3ffff00

def z257 : W := mkw 0x8f0282404a804888 0x23c0a09012a01222 0x9d00c0408cc08fff 0xe7403010233023ff

def z258 : W := mkw 0x0020012000000000 0x0008004800000000 0xeae003b800000000 0x3ab800ee00000000

def z259 : W := mkw 0x17d7a00002e66800 0x85f5e80000b99a00 0xe7ff000003ff7000 0x39ffc00000ffdc00

def z260 : W := mkw 0x40412488111bb330 0x101049220446eccc 0xf6e33c00033ff332 0xbdb8cf0000cffccc

def z261 : W := mkw 0x23bc5f7f84788554 0x08ef17dfe11e2155 0xfffcffff8cf88fff 0xffff3fffe33e23ff

def z262 : W := mkw 0x139ad00000000000 0x04e6b40000000000 0x011cc00000000000 0x0047300000000000

def z263 : W := mkw 0x202003ed010903c1 0x080800fb404240f0 0xeee003ff033f03c3 0x3bb800ffc0cfc0f0

def z264 : W := mkw 0x004124801112b220 0x001049200444ac88 0xfee33f80f33ff332 0xbfb8cfe03ccffccc

def z265 : W := mkw 0x14dd740002f6ec00 0x85375d0000bdbb00 0x24fc3c0003fffc00 0x093f0f0000ffff00

def z266 : W := mkw 0x239402c503e402c1 0x08e500b140f900b0 0xcf1c03c703c003c3 0x33c700f1c0f000f0

def z267 : W := mkw 0x3ffbfb76ee866800 0xcffefeddbba19a00 0xfbffffffff077000 0x3effffffffc1dc00

def z268 : W := mkw 0x40652db9b17bb370 0x10194b6e6c5eecdc 0xffff3ffff3fff3f3 0xbfffcffffcfffcfc

def z269 : W := mkw 0x23b40ffd83fd83d1 0x08ed03ff60ff60f4 0xfffc3fff83ff83f3 0xbfff0fffe0ffe0fc

def z270 : W := mkw 0x00000c9891189330 0x00000326244624cc 0xfe033fb8f338f332 0xbf80cfee3cce3ccc

def z271 : W := mkw 0x3bffff7fec788554 0x4effffdffb1e2155 0xfbfffffffc380000 0x3effffffff0e0000

def z272 : W := mkw 0x8f0282404a804888 0x23c0a09012a01222 0xd703c0400fc0fccd 0x75c0f01003f03f33

def z273 : W := mkw 0x0000081b84080154 0x00000206e1020055 0x9d00c07f8cc08fff 0xe740301fe33023ff

def z274 : W := mkw 0x17fff5a803ffef00 0x85fffd6a00fffbc0 0xffffffb803ffff02 0x3fffffee00ffffc0

def z275 : W := mkw 0x14dff4000076ec00 0x8537fd00001dbb00 0x30fffc00003ffc00 0x0c3fff00000fff00

def z276 : W := mkw 0x00085c1a84188110 0x00021706a1062044 0xbd1cfc7f8c388332 0xaf473f1fe30e20cc

def z277 : W := mkw 0x0445240002f6ec00 0x8111490000bdbb00 0xf6e33c0003fffc00 0x3db8cf0000ffff00

def z278 : W := mkw 0x40612dbbb51bb374 0x10184b6eed46ecdd 0xfee33fffff3ff3ff 0xffb8cfffffcffcff

def z279 : W := mkw 0x23bc5fff87fd87d5 0x08ef17ffe1ff61f5 0xfffcffff8fff8fff 0xffff3fffe3ffe3ff

def z280 : W := mkw 0x0b0ada52cc000000 0x02c2b694b3000000 0xfb1ffffffc000000 0x3ec7ffffff000000

def z281 : W := mkw 0x2bb40bffefed03c1 0x4aed02fffbfb40f0 0xeffc03ffffff03c3 0x3bff00ffffffc0f0

def z282 : W := mkw 0x00085c1284108414 0x00021704a1042105 0x00003c0000000000 0x00000f0000000000

def z283 : W := mkw 0x8f0ede5bcef8cddc 0x23c3b796f3be3377 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z284 : W := mkw 0x0000008011001220 0x0000002004400488 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z285 : W := mkw 0x40652db9b3ffb3f1 0x10194b6e6cffecfc 0xfee33fb8f3fff3f3 0xbfb8cfee3cfffcfc

def z286 : W := mkw 0x0802800048000000 0x0200a00012000000 0x1003c000fc000000 0x0400f0003f000000

def z287 : W := mkw 0x030002c003800280 0x00c000b000e000a0 0x4200038003000000 0x108000e000c00000

def z288 : W := mkw 0x17d3a4000296e800 0x85f4e90000a5ba00 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z289 : W := mkw 0x28200bffed0903c1 0x4a0802fffb4240f0 0x080003fffc0003c3 0x020000ffff0000f0

def z290 : W := mkw 0x030002c0138012a0 0x00c000b004e004a8 0xdf0303c0f3c0f3f3 0xb7c0c0f03cf03cfc

def z291 : W := mkw 0x2020012d00090141 0x0808004b40024050 0x0000003f00000000 0x0000000fc0000000

def z292 : W := mkw 0x3bf3a36468000000 0x4efce8d91a000000 0xdbe3c3c0fc000000 0x36f8f0f03f000000

def z293 : W := mkw 0x0000040000108000 0x0000010000042000 0xb4003c0000388000 0x2d000f00000e2000

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x9900c0408c000000 0x2640301023000000

def z295 : W := mkw 0xcf6ffffbfffbfffc 0x33dbfffefffeffff 0xffffffffffffffff 0xffffffffffffffff

def z296 : W := mkw 0x3bfffb76eee40000 0x4efffeddbbb90000 0xffffffffffff0000 0x3fffffffffffc000

def z297 : W := mkw 0x0004040900788554 0x00010102401e2155 0xad1c007f00f88fff 0xeb47001fc03e23ff

def z298 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x301cfc3f8c388c3c 0xcc073f0fe30e230f

def z299 : W := mkw 0x37fff52d02ffed41 0x8dfffd4b40bffb50 0xf7fffc3f03fffc00 0x3dffff0fc0ffff00

def z300 : W := mkw 0x0000008011001220 0x0000002004400488 0x08000380f0000332 0x820000e03c0000cc

def z301 : W := mkw 0x4763adb8b39bfb30 0x11d8eb6e2ce6fecc 0xffe3ffb8f3ffff32 0xbff8ffee3cffffcc

def z302 : W := mkw 0x030002c003800280 0x00c000b000e000a0 0xdf00c3c08fc08fff 0xf7c030f023f023ff

def z303 : W := mkw 0x000c500b04680544 0x00031402c11a0151 0xad1cc07f0cf80fcf 0x6b47301fc33e03f3

def z304 : W := mkw 0xbf9ad2464e804888 0x6fe6b49193a01222 0x011cc0470cc00ccd 0x40473011c3300333

def z305 : W := mkw 0x0000081b84080154 0x00000206e1020055 0x0000003f00000000 0x0000000fc0000000

def z306 : W := mkw 0x20bc5d3f847d8555 0x082f174fe11f6155 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z307 : W := mkw 0x040c540002f6ec00 0x8103150000bdbb00 0xb51cfc0003fffc00 0x2d473f0000ffff00

def z308 : W := mkw 0xcf63a3e07b837aa8 0x33d8e8f81ee0deaa 0xdfe3c3c0ffc7ffff 0xf7f8f0f03ff1ffff

def z309 : W := mkw 0x9fdff6c05bf6fea8 0xa7f7fdb016fdbfaa 0xf7ffff8073fffc00 0x3dffffe01cffff00

def z310 : W := mkw 0x28612b76ec000000 0x4a184addbb000000 0xfae33ffffc000000 0x3eb8cfffff000000

def z311 : W := mkw 0xc4612db8b39bfbb8 0x31184b6e2ce6feee 0xfee33fb8f3ffffff 0xffb8cfee3cffffff

def z312 : W := mkw 0x17d3a00002866800 0x85f4e80000a19a00 0xd7e3c00003c7fc00 0x35f8f00000f1ff00

def z313 : W := mkw 0x0000000304000044 0x00000000c1000011 0x000000470c0000cd 0x40000011c3000033

def z314 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0x46e0038003ff03c3 0x11b800e000ffc0f0

def z315 : W := mkw 0x030402c903e803c0 0x00c100b240fa00f0 0xef1c03ff03f803c3 0x3bc700ffc0fe00f0

def z316 : W := mkw 0x3b9ed2474ee400c1 0x4ee7b491d3b90030 0x011cc0470cc000c1 0x00473011c3300030

def z317 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xfffcc3ff8fff8fff 0xffff30ffe3ffe3ff

def z318 : W := mkw 0x23b0036400000000 0x08ec00d900000000 0x42e0038000000000 0x10b800e000000000

def z319 : W := mkw 0x7bfbfbfefd091330 0x5efefeffbf4244cc 0xfbfffffffc000332 0xbeffffffff0000cc

def z320 : W := mkw 0x000c5c9b95789774 0x00031726e55e25dd 0xff1ffffffff8ffff 0xffc7fffffffe3fff

def z321 : W := mkw 0x032003e803890380 0x00c800fa00e240e0 0xefe003f803ff03c3 0x3bf800fe00ffc0f0

def z322 : W := mkw 0x040004000012ec00 0x810001000004bb00 0x000000000000fc00 0x0000000000003f00

def z323 : W := mkw 0x002c5dbb85798754 0x000b176ee15e61d5 0xfffcffff8fff8fff 0xffff3fffe3ffe3ff

def z324 : W := mkw 0x37f3a3e403876a81 0x8dfce8f900e1daa0 0x42e3038003077000 0x10b8c0e000c1dc00

def z325 : W := mkw 0x23f12b74a0000000 0x08fc4add28000000 0xfbff3ffff0000000 0x3effcffffc000000

def z326 : W := mkw 0x0000000010001020 0x0000000004000408 0x10030000f000f030 0x8400c0003c003c0c

def z327 : W := mkw 0x0796800002e44800 0x01e5a00000b91200 0xf7ffc00003fffc00 0x3dfff00000ffff00

def z328 : W := mkw 0x2820036468000000 0x4a0800d91a000000 0x0000038070000000 0x000000e01c000000

def z329 : W := mkw 0x000c540900788554 0x00031502401e2155 0xb51cfc0000f88fff 0xed473f00003e23ff

def z330 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x0900c3c0fcc00fff 0xc24030f03f3003ff

def z331 : W := mkw 0x68200bfefd091330 0x5a0802ffbf4244cc 0x080003fffc000332 0x820000ffff0000cc

def z332 : W := mkw 0x3bfbfbf6fd001220 0x4efefefdbf400488 0xffffffffff00f332 0xbfffffffffc03ccc

def z333 : W := mkw 0x9fdffedbdffefffc 0xa7f7ffb6f7ffbfff 0xffffffffffffffff 0xffffffffffffffff

def z334 : W := mkw 0x004124000012a000 0x001049000004a800 0x20e03c00003f0000 0x08380f00000fc000

def z335 : W := mkw 0x13d3a00000000000 0x04f4e80000000000 0x42e3000000000000 0x10b8c00000000000

def z336 : W := mkw 0x28200b7fec080154 0x4a0802dffb020055 0x080003fffc0003ff 0xc20000ffff0000ff

def z337 : W := mkw 0x039c5c1b86fc8554 0x00e71706e1bf2155 0xfffcfc7f8fff8fff 0xffff3f1fe3ffe3ff

def z338 : W := mkw 0x20b403ed016d03c1 0x082d00fb405b40f0 0x28fc03ff003f03c3 0x0a3f00ffc00fc0f0

def z339 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0x62fc03bf033f0000 0x18bf00efc0cfc000

def z340 : W := mkw 0x40200938a0090110 0x1008024e28024044 0x0000003800000000 0x0000000e00000000

def z341 : W := mkw 0x9fd3a2c05b867aa8 0xa7f4e8b016e19eaa 0xdfe3c3c0ffc7ffff 0xf7f8f0f03ff1ffff

def z342 : W := mkw 0x8f9682c05be45aa8 0x23e5a0b016f916aa 0xffffc3c0ffffffff 0xfffff0f03fffffff

def z343 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0xeee003b8f33f0332 0xbbb800ee3ccfc0cc

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x9500c00000c08c00 0x2540300000302300

def z345 : W := mkw 0x8c02800048004808 0x2300a00012001202 0x0000c0000c000c0c 0x4000300003000303

def z346 : W := mkw 0x37f7a3ed03ef6bc1 0x8dfde8fb40fbdaf0 0xefff03ff03ff73c3 0x3bffc0ffc0ffdcf0

def z347 : W := mkw 0x0394000902ec0140 0x00e5000240bb0050 0xeffc007f03ff03c3 0x3bff001fc0ffc0f0

def z348 : W := mkw 0x0300024002800080 0x00c0009000a00020 0x0100004000c000c1 0x0040001000300030

def z349 : W := mkw 0x57fffd38a2ffed10 0x95ffff4e28bffb44 0xf7fffc3803fffc00 0x3dffff0e00ffff00

def z350 : W := mkw 0xa7b403ed13ed5be9 0x29ed00fb44fb56fa 0xeffc03ff03ffffff 0xfbff00ffc0ffffff

def z351 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0x21fcfc0000ff0c00 0x087f3f00003fc300

def z352 : W := mkw 0xbffff7ed5bffffe9 0xaffffdfb56fffffa 0xffffffffffffffff 0xffffffffffffffff

def z353 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0x24e03c38033ff332 0x89380f0e00cffccc

def z354 : W := mkw 0x0000000900080140 0x0000000240020050 0x0800007f000003c3 0x0200001fc00000f0

def z355 : W := mkw 0x1c4bfc12ec12ec00 0xc712ff04bb04bb00 0x1003fc00fc00fc00 0x0400ff003f003f00

def z356 : W := mkw 0x002001a811091320 0x0008006a044244c8 0xfee303b8f33ff332 0xbfb8c0ee3ccffccc

def z357 : W := mkw 0x0008500204000000 0x0002140081000000 0x011cc0470c000000 0x00473011c3000000

def z358 : W := mkw 0x0000008011001220 0x0000002004400488 0x4203038073007000 0x1080c0e01cc01c00

def z359 : W := mkw 0x0300000002800000 0x00c0000000a00000 0xc700000003c00000 0x31c0000000f00000

def z360 : W := mkw 0xdffffff8fbffffb8 0xb7fffffe3effffee 0xfffffff8ffffffff 0xfffffffe3fffffff

def z361 : W := mkw 0x13dbf81284000000 0x04f6fe04a1000000 0xfbfffc7f8c000000 0x3effff1fe3000000

def z362 : W := mkw 0x43f52db8b3ffb330 0x10fd4b6e2cffeccc 0xffff3fb8f3fff332 0xbfffcfee3cfffccc

def z363 : W := mkw 0x0302800000000000 0x00c0a00000000000 0xd303c00000000000 0x34c0f00000000000

def z364 : W := mkw 0x0800024048000000 0x0200009012000000 0x080003c0fc000000 0x020000f03f000000

def z365 : W := mkw 0x37fff76402f6ec00 0x8dfffdd900bdbb00 0xffffffff03fffc00 0x3fffffffc0ffff00

def z366 : W := mkw 0x60f52d3da07fa151 0x183d4b4f681fe854 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z367 : W := mkw 0xbffffffffff8dffc 0x6ffffffffffe37ff 0xfffffffffff8ffff 0xfffffffffffe3fff

def z368 : W := mkw 0x070282c003804a80 0x01c0a0b000e012a0 0xdf03c3c003c0ffc3 0x37c0f0f000f03ff0

def z369 : W := mkw 0xcc63adb8f91bfb38 0x3318eb6e3e46fece 0xfee3ffb8ff3fff3e 0xffb8ffee3fcfffcf

def z370 : W := mkw 0x40612db8a11ba310 0x10184b6e2846e8c4 0xeee03fb8033f0302 0x3bb80fee00cfc0c0

def z371 : W := mkw 0x30f1212420000000 0x4c3c484908000000 0x00e0000000000000 0x0038000000000000

def z372 : W := mkw 0x3bbadb76ec000000 0x4eeeb6ddbb000000 0x091cc3fffc000000 0x024730ffff000000

def z373 : W := mkw 0x406d7d3ba47ba554 0x101b5f4ee91ee955 0xbdfcfc7f8cff8fff 0xef7f3f1fe33fe3ff

def z374 : W := mkw 0xc4000488139bfbb8 0x3100012204e6feee 0x0400000003ffffff 0xc100000000ffffff

def z375 : W := mkw 0x039c540002f48400 0x00e7150000bd2100 0xf7fcfc0003ff8c00 0x3dff3f0000ffe300

def z376 : W := mkw 0xbff3a3e47b805aa8 0x6ffce8f91ee016aa 0xdfe3c3c0ffc0ffff 0xf7f8f0f03ff03fff

def z377 : W := mkw 0x27b407ed03ffefc1 0x89ed01fb40fffbf0 0xeffc03ff03ffffc3 0x3bff00ffc0fffff0

def z378 : W := mkw 0xcf43aed0fb92fab8 0x33d0ebb43ee4beae 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z379 : W := mkw 0x37fff7e403f7ee81 0x8dfffdf900fdfba0 0xf7ffff8003fffc00 0x3dffffe000ffff00

def z380 : W := mkw 0x9fd3a2c05b867aa8 0xa7f4e8b016e19eaa 0x42e3038073077000 0x10b8c0e01cc1dc00

def z381 : W := mkw 0x000c5c9b87fd87d5 0x00031726e1ff61f5 0xbd1cfc7f8fff8fff 0xef473f1fe3ffe3ff

def z382 : W := mkw 0x0004000102e400c1 0x0001000040b90030 0x0000000000c000c1 0x0000000000300030

def z383 : W := mkw 0x23b407ed03fd87d5 0x08ed01fb40ff61f5 0xeffc03ff03ff8fff 0xfbff00ffc0ffe3ff

def z384 : W := mkw 0x30fd7d36a476a400 0xcc3f5f4da91da900 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z385 : W := mkw 0x8c0edc1bdc78dd7c 0x2303b706f71e375f 0xbd1ffc7ffcf8ffff 0xef47ff1fff3e3fff

def z386 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x0500c0400fc0ffff 0xc140301003f03fff

def z387 : W := mkw 0x8c02808059005a28 0x2300a0201640168a 0xde03c380ff00ff3e 0xf780f0e03fc03fcf

def z388 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0xbc1c3c3f80388332 0xaf070f0fe00e20cc

def z389 : W := mkw 0x37ffffff87ffefd5 0x8dffffffe1fffbf5 0xffffffff8fffffff 0xffffffffe3ffffff

def z390 : W := mkw 0x3bf7a3ed6bed03c1 0x4efde8fb5afb40f0 0xefff03ff73ff03c3 0x3bffc0ffdcffc0f0

def z391 : W := mkw 0x3ffbff76ec12ec00 0xcffeffddbb04bb00 0xfbfffffffc00fc00 0x3effffffff003f00

def z392 : W := mkw 0x17dff00002e44c00 0x85f7fc0000b91300 0xf3fffc0000c00c00 0x3cffff0000300300

def z393 : W := mkw 0x3b9ad2464c000000 0x4ee6b49193000000 0xdb1fc3c7fc000000 0x36c7f0f1ff000000

def z394 : W := mkw 0x406d7d3ba47ba554 0x101b5f4ee91ee955 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z395 : W := mkw 0x282c5f7fec788554 0x4a0b17dffb1e2155 0xbd1cfffffcf88fff 0xef473fffff3e23ff

def z396 : W := mkw 0x3ffbfb76ee804800 0x4ffefeddbba01200 0xffffffffffc0fc00 0x3ffffffffff03f00

def z397 : W := mkw 0x37bed3ed03ed4fc1 0x8defb4fb40fb53f0 0xeffcc3ff03ff0fc3 0x3bff30ffc0ffc3f0

def z398 : W := mkw 0x40612d30b012b030 0x10184b4c2c04ac0c 0xfae33fb8f000f030 0xbeb8cfee3c003c0c

def z399 : W := mkw 0x23b003ed038d03c1 0x08ec00fb40e340f0 0x4ae003ff030703c3 0x12b800ffc0c1c0f0

def z400 : W := mkw 0x8c02800058005828 0x2300a0001600160a 0x0003000070007000 0x0000c0001c001c00

def z401 : W := mkw 0x10dd74000076a400 0x84375d00001da900 0xb5fcfc0000ff8c00 0x2d7f3f00003fe300

def z402 : W := mkw 0x00040c1b84788554 0x00010306e11e2155 0x0c00007f8cf88fff 0xc300001fe33e23ff

def z403 : W := mkw 0x402c5dbbb5799774 0x100b176eed5e65dd 0xbd1cfffffcf88fff 0xef473fffff3e23ff

def z404 : W := mkw 0x0008581284000000 0x00021604a1000000 0xbd1cfc7f8cc08fff 0xef473f1fe33023ff

def z405 : W := mkw 0x23b85b7684000000 0x08ee16dda1000000 0xfbfcffff8c000000 0x3eff3fffe3000000

def z406 : W := mkw 0x40412c90b112b230 0x10104b242c44ac8c 0xde033f80f300f332 0xb780cfe03cc03ccc

def z407 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x211cfc7f0cf80ccd 0x48473f1fc33e0333

def z408 : W := mkw 0x33fbf936a4000000 0x4cfefe4da9000000 0xf3fffc3f00000000 0x3cffff0fc0000000

def z409 : W := mkw 0x0000081284000014 0x00000204a1000005 0x000000008c00003c 0xc00000002300000f

def z410 : W := mkw 0x8f0282404a804888 0x23c0a09012a01222 0xdb03c3c0fcc00ccd 0x76c0f0f03f300333

def z411 : W := mkw 0x0702800002804800 0x01c0a00000a01200 0xdf03c0408fc0ffff 0xf7c0f01023f03fff

def z412 : W := mkw 0x40612d38a01ba110 0x10184b4e2806e844 0xbce03c38803f8332 0xaf380f0e200fe0cc

def z413 : W := mkw 0x8800000058001028 0x220000001600040a 0x00000000fc00003c 0xc00000003f00000f

def z414 : W := mkw 0x8b0282c0590012a8 0x22c0a0b0164004aa 0xdb03c3c0fc0003ff 0xf6c0f0f03f0000ff

def z415 : W := mkw 0x40612d38b01bb130 0x10184b4e2c06ec4c 0x30e33c38f03ff030 0x8c38cf0e3c0ffc0c

def z416 : W := mkw 0x3fffff7feefeed54 0xcfffffdffbbfbb55 0xffffffffffffffff 0xffffffffffffffff

def z417 : W := mkw 0x40040489117bb774 0x10010122445eeddd 0x0400000003ffffff 0xc100000000ffffff

def z418 : W := mkw 0x00085c1b84188554 0x00021706e1062155 0x1800fc7f8c008fff 0xc6003f1fe30023ff

def z419 : W := mkw 0x402001a031011220 0x100800680c404488 0x0000038070000000 0x000000e01c000000

def z420 : W := mkw 0x3bfbff7eec188110 0x4efeffdfbb062044 0xfffffffffc388332 0xbfffffffff0e20cc

def z421 : W := mkw 0x1b4bfa52ec000000 0x46d2fe94bb000000 0xdb03ffc0fc000000 0x36c0fff03f000000

def z422 : W := mkw 0x10d1200000062000 0x8434480000018800 0x00e0000000070000 0x003800000001c000

def z423 : W := mkw 0x0008581284000000 0x00021604a1000000 0x201c3c3f00000000 0x08070f0fc0000000

def z424 : W := mkw 0x13fbf930a0000000 0x04fefe4c28000000 0xfbffffb8f0000000 0x3effffee3c000000

def z425 : W := mkw 0x20b0012400050001 0x082c004900014000 0x00e0000000070000 0x003800000001c000

def z426 : W := mkw 0x40000488111bb330 0x100001220446eccc 0xde030380f33ff332 0xb780c0e03ccffccc

def z427 : W := mkw 0x8f0682c95be85be8 0x23c1a0b256fa16fa 0xff1fc3fffff8ffff 0xffc7f0fffffe3fff

def z428 : W := mkw 0x179ed40002f6ec00 0x85e7b50000bdbb00 0x051cc00003fffc00 0x0147300000ffff00

def z429 : W := mkw 0x0743a4000292e800 0x01d0e90000a4ba00 0xf7e3fc0003fffc00 0x3df8ff0000ffff00

def z430 : W := mkw 0x406129b8b10b3330 0x10184a6e2c42cccc 0x4ae303b8f3077332 0x92b8c0ee3cc1dccc

def z431 : W := mkw 0x40000810b0001030 0x100002042c00040c 0x00000000f0000030 0x800000003c00000c

def z432 : W := mkw 0xcc43ac10f812f838 0x3310eb043e04be0e 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z433 : W := mkw 0x30fd7d3fa4788554 0x4c3f5f4fe91e2155 0x20fc3c3f00380000 0x083f0f0fc00e0000

def z434 : W := mkw 0x3bdbf2464c000000 0x4ef6fc9193000000 0xf3fffc470c000000 0x3cffff11c3000000

def z435 : W := mkw 0x9f4bfad2ff805aa8 0x67d2feb4bfe016aa 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z436 : W := mkw 0x400c5c9b957bb774 0x10031726e55eeddd 0xbd1cfc7f8fffffff 0xef473f1fe3ffffff

def z437 : W := mkw 0x3bfbff76ec108414 0x4efeffddbb042105 0xfbfffffffc008c3c 0xfeffffffff00230f

def z438 : W := mkw 0x50fd7db8b17fb730 0x943f5f6e2c5fedcc 0xfeff3fb8f33ff332 0xbfbfcfee3ccffccc

def z439 : W := mkw 0x404d7c1bb47ab574 0x10135f06ed1ead5d 0xbd1ffc7ffcf8ffff 0xef47ff1fff3e3fff

def z440 : W := mkw 0x880002c0590012a8 0x220000b0164004aa 0x9d00c3c0fcc08fff 0xe74030f03f3023ff

def z441 : W := mkw 0x4061212020032000 0x101848480800c800 0x00e0000000070000 0x003800000001c000

def z442 : W := mkw 0x3fffffffefffefc1 0xcffffffffbfffbf0 0xffffffffffffffc3 0x3ffffffffffffff0

def z443 : W := mkw 0x3bfbff76ec12a000 0x4efeffddbb04a800 0xffffffffff3ff000 0x3fffffffffcffc00

def z444 : W := mkw 0x30fd7d3fa4788554 0x4c3f5f4fe91e2155 0xbdfcfc7f8cf88fff 0xef7f3f1fe33e23ff

def z445 : W := mkw 0x3bfbfbffed0903c1 0x4efefefffb4240f0 0xfbfffffffc0003c3 0x3effffffff0000f0

def z446 : W := mkw 0x0300024000000000 0x00c0009000000000 0xcb0003c000000000 0x32c000f000000000

def z447 : W := mkw 0x7bf3a3e479033220 0x5efce8f91e40cc88 0x42e3038073077000 0x10b8c0e01cc1dc00

def z448 : W := mkw 0x2394024d02ec01c1 0x08e5009340bb0070 0xad1c007f00f803c3 0x2b47001fc03e00f0

def z449 : W := mkw 0x000c500304600444 0x00031400c1180111 0x9d1cc0478cc08fff 0xe7473011e33023ff

def z450 : W := mkw 0x004d7c1b847aa554 0x00135f06e11ea955 0xfffffc7f8fffffff 0xffffff1fe3ffffff

def z451 : W := mkw 0x8400008013805aa8 0x2100002004e016aa 0x9d00c0408fc0ffff 0xe740301023f03fff

def z452 : W := mkw 0x0000081880080110 0x0000020620020044 0x0800003880000332 0x8200000e200000cc

def z453 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0xde030380f300f332 0xb780c0e03cc03ccc

def z454 : W := mkw 0x006129b8a1090300 0x00184a6e284240c0 0xfee33fb8f33f0302 0x3fb8cfee3ccfc0c0

def z455 : W := mkw 0x40412c10a012a010 0x10104b042804a804 0x00003c0000000000 0x00000f0000000000

def z456 : W := mkw 0x23b4036502e400c1 0x08ed00d940b90030 0xebfc03ff00c000c1 0x3aff00ffc0300030

def z457 : W := mkw 0x7ffffffeffffff30 0xdfffffffbfffffcc 0xffffffffffffff32 0xbfffffffffffffcc

def z458 : W := mkw 0x406129b8b1091330 0x10184a6e2c4244cc 0xfae33fb8f0000332 0xbeb8cfee3c0000cc

def z459 : W := mkw 0x000004000012a000 0x000001000004a800 0x04000000033ff000 0x0100000000cffc00

def z460 : W := mkw 0x0004040000708400 0x00010100001c2100 0x0400000000f88c00 0x01000000003e2300

def z461 : W := mkw 0x104bf00000000000 0x0412fc0000000000 0x1003fc0000000000 0x0400ff0000000000

def z462 : W := mkw 0x179ed00002e44c00 0x85e7b40000b91300 0xd71fc00003c0fc00 0x35c7f00000f03f00

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000408c0003ff 0xc2000010230000ff

def z464 : W := mkw 0xaf9682c55be45ae9 0x2be5a0b156f916ba 0xdf1fc3c7ffc0ffff 0xf7c7f0f1fff03fff

def z465 : W := mkw 0x17dbf00002804800 0x05f6fc0000a01200 0xf7fffc0003c0fc00 0x3dffff0000f03f00

def z466 : W := mkw 0x8f0ed2c35fe05eec 0x23c3b4b0d7f817bb 0xdf1fc3c7ffc0ffff 0xf7c7f0f1fff03fff

def z467 : W := mkw 0x000c500304600444 0x00031400c1180111 0x001c000700000000 0x00070001c0000000

def z468 : W := mkw 0x23bc5fff87fd87d5 0x08ef17ffe1ff61f5 0xeffc3fff03ff03c3 0x3bff0fffc0ffc0f0

def z469 : W := mkw 0x8f02824058005828 0x23c0a0901600160a 0xdb03c3c0fc00fc3c 0xf6c0f0f03f003f0f

def z470 : W := mkw 0x3098500604000000 0x4c26140181000000 0x001c000700000000 0x00070001c0000000

def z471 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0xdb03c3c0ff007000 0x36c0f0f03fc01c00

def z472 : W := mkw 0x0004000002e40000 0x0001000000b90000 0x0400000003ff0000 0x0100000000ffc000

def z473 : W := mkw 0x23f527ed03ffa3c1 0x08fd49fb40ffe8f0 0xffff3fff03fff3c3 0x3fffcfffc0fffcf0

def z474 : W := mkw 0x3bdbfa56ec000000 0x4ef6fe95bb000000 0x111ffc47fc000000 0x0447ff11ff000000

def z475 : W := mkw 0x174bf4000292ec00 0x85d2fd0000a4bb00 0xd703fc0003c0fc00 0x35c0ff0000f03f00

def z476 : W := mkw 0x8f0686c05bf6fea8 0xa3c1a1b016fdbfaa 0xdf03c3c0ffffffff 0xf7c0f0f03fffffff

def z477 : W := mkw 0x13dff00002e40000 0x04f7fc0000b90000 0xf7fffc0003ff0000 0x3dffff0000ffc000

def z478 : W := mkw 0x9c4bf812fc005828 0x6712fe04bf00160a 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z479 : W := mkw 0x23b4036d006d0141 0x08ed00db401b4050 0xebfc03ff003f0000 0x3aff00ffc00fc000

def z480 : W := mkw 0x3bffffffeffd87d5 0x4efffffffbff61f5 0xffffffffffff8fff 0xffffffffffffe3ff

def z481 : W := mkw 0x0000008003850281 0x0000002000e140a0 0x0000000003070000 0x0000000000c1c000

def z482 : W := mkw 0x33fd77ed03ffa7c1 0x8cff5dfb40ffe9f0 0xeffc3fff03ff03c3 0x3bff0fffc0ffc0f0

def z483 : W := mkw 0x0008540000108400 0x0002150000042100 0x1000fc0000008c00 0x04003f0000002300

def z484 : W := mkw 0x17d7a40002f6ec00 0x85f5e90000bdbb00 0x46e3000003fffc00 0x11b8c00000ffff00

def z485 : W := mkw 0x60200bfdb10913f1 0x180802ff6c4244fc 0x080003fff00003f3 0x820000fffc0000fc

def z486 : W := mkw 0x70f97d3ea41ba110 0x5c3e5f4fa906e844 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z487 : W := mkw 0x0400000002866800 0x8100000000a19a00 0x0000000003077000 0x0000000000c1dc00

def z488 : W := mkw 0x00412810a0000000 0x00104a0428000000 0x10033c00f0000000 0x0400cf003c000000

def z489 : W := mkw 0x180ad0024c000000 0x4602b40093000000 0x0000c0000c000000 0x0000300003000000

def z490 : W := mkw 0x2b228b76ec000000 0x4ac8a2ddbb000000 0xdb03c3fffc000000 0x36c0f0ffff000000

def z491 : W := mkw 0x0004000100600040 0x0001000040180010 0x011c004700c000c1 0x00470011c0300030

def z492 : W := mkw 0x60612ffdb11bb3f1 0x18184bff6c46ecfc 0xfee33ffff33ff3f3 0xbfb8cffffccffcfc

def z493 : W := mkw 0x8702808013805aa8 0x21c0a02004e016aa 0xd703c00003c0ffff 0xf5c0f00000f03fff

def z494 : W := mkw 0x57f3a1a033877a20 0x95fce8680ce1de88 0x42e3038073077000 0x10b8c0e01cc1dc00

def z495 : W := mkw 0x03d5240002f6a000 0x00f5490000bda800 0xf7ff3c0003fff000 0x3dffcf0000fffc00

def z496 : W := mkw 0x006d7d3ba4788554 0x001b5f4ee91e2155 0xfffffffffcf88fff 0xffffffffff3e23ff

def z497 : W := mkw 0x406129b0b1033220 0x10184a6c2c40cc88 0xfae33fb8f3077000 0x3eb8cfee3cc1dc00

def z498 : W := mkw 0x0b0282c059001220 0x02c0a0b016400488 0xdf03c3c0ff00f332 0xb7c0f0f03fc03ccc

def z499 : W := mkw 0x039402c003e40280 0x00e500b000f900a0 0xeffc03c003ff03c3 0x3bff00f000ffc0f0

def z500 : W := mkw 0x239c5e5f86fc85d5 0x08e71797e1bf2175 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z501 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0xad1c3c7f00f803c3 0x2b470f1fc03e00f0

def z502 : W := mkw 0xcf63aff8fb9bfbb8 0x33d8ebfe3ee6feee 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z503 : W := mkw 0xa8200bf6fd0012a8 0x6a0802fdbf4004aa 0x080003fffc0003ff 0xc20000ffff0000ff

def z504 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x5203c380ff00fc3c 0xd480f0e03fc03f0f

def z505 : W := mkw 0x00200db881198310 0x0008036e204660c4 0xfee03fb8833f8332 0xbfb80fee20cfe0cc

def z506 : W := mkw 0x40200db8b11bb330 0x1008036e2c46eccc 0x0c0003b8f33ff332 0x830000ee3ccffccc

def z507 : W := mkw 0x13dff4000076a400 0x84f7fd00001da900 0xf3fffc00003f0000 0x3cffff00000fc000

def z508 : W := mkw 0x28285b76ec000000 0x4a0a16ddbb000000 0xb91cfffffc000000 0x2e473fffff000000

def z509 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x4603038073c0ffff 0xd180c0e01cf03fff

def z510 : W := mkw 0x23bc53ef07ed07c5 0x08ef14fbc1fb41f1 0xeffcc3ff0fff0fcf 0x7bff30ffc3ffc3f3

def z511 : W := mkw 0x000c5c1284708400 0x00031704a11c2100 0xbd1cfc7f8cf88c00 0x2f473f1fe33e2300

def z512 : W := mkw 0x8f0682c95bed5be9 0x23c1a0b256fb56fa 0xdf03c3c0ffffffff 0xf7c0f0f03fffffff

def z513 : W := mkw 0x0706840002f6ec00 0x81c1a10000bdbb00 0xd703c00003fffc00 0x35c0f00000ffff00

def z514 : W := mkw 0x20200bff850903d5 0x080802ffe14240f5 0x080003ff8c0003ff 0xc20000ffe30000ff

def z515 : W := mkw 0x33fbf36400000000 0x0cfefcd900000000 0xfbffffff00000000 0x3effffffc0000000

def z516 : W := mkw 0x0404000002e44c00 0x8101000000b91300 0x0000000000c00c00 0x0000000000300300

def z517 : W := mkw 0xc8612ff8f91bb3b8 0x32184bfe3e46ecee 0xfee33ff8ff3ff3ff 0xffb8cffe3fcffcff

def z518 : W := mkw 0x030c5edb87f887d4 0x00c317b6e1fe21f5 0xff1cffff8ff88fff 0xffc73fffe3fe23ff

def z519 : W := mkw 0x9fdff4005af6fc28 0xa7f7fd0016bdbf0a 0xf7fffc00fffffc3c 0xfdffff003fffff0f

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0xa91c007f00000000 0x2a47001fc0000000

def z521 : W := mkw 0x0000081080000000 0x0000020420000000 0xb8003c3880000000 0x2e000f0e20000000

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000000c08fff 0xc1000000003023ff

def z523 : W := mkw 0x0b0282c04b800280 0x02c0a0b012e000a0 0xdf03c3c0ffc003c3 0x37c0f0f03ff000f0

def z524 : W := mkw 0x3bfbfbfeed090300 0x4efefeffbb4240c0 0xffffffffff3f0302 0x3fffffffffcfc0c0

def z525 : W := mkw 0x0000008011001220 0x0000002004400488 0x040000000300f332 0x8100000000c03ccc

def z526 : W := mkw 0x57fff5a033f7fe20 0x95fffd680cfdff88 0xf7ffff8073fffc00 0x3dffffe01cffff00

def z527 : W := mkw 0x33fd7bffa7ed03c1 0x4cff5effe9fb40f0 0xeffc3fff03ff03c3 0x3bff0fffc0ffc0f0

def z528 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x4303c3c07fc07ccd 0x50c0f0f01ff01f33

def z529 : W := mkw 0x63fd7fffb7ffb7f5 0x18ff5fffedffedfd 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x546bfdb8b11bff30 0x951aff6e2c46ffcc 0xfee3ffb8f33fff32 0xbfb8ffee3ccfffcc

def z531 : W := mkw 0x104974000012a400 0x84125d000004a900 0x00003c0000000000 0x00000f0000000000

def z532 : W := mkw 0x33f97b76a4000000 0x4cfe5edda9000000 0xebfc3fff00000000 0x3aff0fffc0000000

def z533 : W := mkw 0x006129b0b1001220 0x00184a6c2c400488 0xfee33fb8f300f332 0xbfb8cfee3cc03ccc

def z534 : W := mkw 0x030402c903ed03c1 0x00c100b240fb40f0 0xcf0003c003ff03c3 0x33c000f000ffc0f0

def z535 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0x62e33fb8733f7000 0x18b8cfee1ccfdc00

def z536 : W := mkw 0x000404000076a400 0x80010100001da900 0x00000000003f0000 0x00000000000fc000

def z537 : W := mkw 0x70f97dbeb51bb330 0x5c3e5f6fad46eccc 0xfeff3fbff33ff332 0xbfbfcfeffccffccc

def z538 : W := mkw 0x0004000900680140 0x00010002401a0050 0x0400000000f803c3 0x01000000003e00f0

def z539 : W := mkw 0x0000040000108414 0x0000010000042105 0x0000000000008c3c 0xc00000000000230f

def z540 : W := mkw 0x40497c12b412b434 0x10125f04ad04ad0d 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z541 : W := mkw 0x179edc1b86fccd54 0x85e7b706e1bf3355 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z542 : W := mkw 0x202403ed016903c1 0x080900fb405a40f0 0xad1c03ff00f803c3 0x2b4700ffc03e00f0

def z543 : W := mkw 0x880002c0590012a8 0x220000b0164004aa 0xde0303c0ff00f3ff 0xf780c0f03fc03cff

def z544 : W := mkw 0xbbfbfbf6fd0012a8 0x6efefefdbf4004aa 0xfbfffffffc0003ff 0xfeffffffff0000ff

def z545 : W := mkw 0x40200db8b1199330 0x1008036e2c4664cc 0xbc003fb8f0388332 0xaf000fee3c0e20cc

def z546 : W := mkw 0x00000089010903c1 0x00000022404240f0 0x00000000000003c3 0x00000000000000f0

def z547 : W := mkw 0xaf228bf6ff805aa8 0x6bc8a2fdbfe016aa 0xdf03c3ffffc0ffff 0xf7c0f0fffff03fff

def z548 : W := mkw 0x0020012800090100 0x0008004a00024040 0x20e00038003f0000 0x0838000e000fc000

def z549 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0xd703c38073c0fc00 0x35c0f0e01cf03f00

def z550 : W := mkw 0x4000008811091330 0x10000022044244cc 0x0000000000000332 0x80000000000000cc

def z551 : W := mkw 0x63f123e4338732a1 0x18fc48f90ce1cca8 0x42e3038073077000 0x10b8c0e01cc1dc00

def z552 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0x62ff3c00033f7000 0x18bfcf0000cfdc00

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0xda030380f0000000 0x3680c0e03c000000

def z554 : W := mkw 0x0b63ab70e8000000 0x02d8eadc3a000000 0xfbe3fff8fc000000 0x3ef8fffe3f000000

def z555 : W := mkw 0x00200930a0000000 0x0008024c28000000 0x080003b8f0000000 0x020000ee3c000000

def z556 : W := mkw 0x7bffffffffffb3f1 0x5effffffffffecfc 0xfffffffffffff3f3 0xbffffffffffffcfc

def z557 : W := mkw 0x97dff48013f6fea8 0xa5f7fd2004fdbfaa 0xf7fffc0003ffffff 0xfdffff0000ffffff

def z558 : W := mkw 0x50fd7d38a07fa510 0x943f5f4e281fe944 0x20fc3c38003f0000 0x083f0f0e000fc000

def z559 : W := mkw 0x002001a001010200 0x0008006800404080 0x42e0038003070000 0x10b800e000c1c000

def z560 : W := mkw 0x000c5c1384708454 0x00031704e11c2115 0x111cfc478cc08cfd 0xc4473f11e330233f

def z561 : W := mkw 0x0000000800080100 0x0000000200020040 0xac00003800380302 0x2b00000e000e00c0

def z562 : W := mkw 0x40000c98911bb330 0x100003262446eccc 0xbc003c38833ff332 0xaf000f0e20cffccc

def z563 : W := mkw 0x402005a8111bb330 0x1008016a0446eccc 0xeee003b8033ff332 0xbbb800ee00cffccc

def z564 : W := mkw 0x0b02824048000000 0x02c0a09012000000 0x0100c0400c000000 0x0040301003000000

def z565 : W := mkw 0x40412c18b01ab130 0x10104b062c06ac4c 0xbc033c38f038f332 0xaf00cf0e3c0e3ccc

def z566 : W := mkw 0x23bc5bff87ed03c1 0x08ef16ffe1fb40f0 0xfffcffff8fff03c3 0x3fff3fffe3ffc0f0

def z567 : W := mkw 0x4004048913ffb3f1 0x1001012244ffecfc 0x0400000003fff3f3 0x8100000000fffcfc

def z568 : W := mkw 0x0390000002840000 0x00e4000000a10000 0x42e0000003070000 0x10b8000000c1c000

def z569 : W := mkw 0x8f0ed6c05bf0dea8 0x23c3b5b016fc37aa 0xff1fffc0fff8ffff 0xffc7fff03ffe3fff

def z570 : W := mkw 0x3bfffb7fec680140 0x4efffedffb1a0050 0xfffffffffcf803c3 0x3fffffffff3e00f0

def z571 : W := mkw 0x9f4bf6c05b92fea8 0xa7d2fdb016e4bfaa 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z572 : W := mkw 0x0394008903ed03c1 0x00e5002240fb40f0 0xe7fc000003ff03c3 0x39ff000000ffc0f0

def z573 : W := mkw 0x30f97936a4000000 0x4c3e5e4da9000000 0xb9fcfc7f8c000000 0x2e7f3f1fe3000000

def z574 : W := mkw 0x3ff3a3646a866800 0xcffce8d91aa19a00 0x42e3038073077000 0x10b8c0e01cc1dc00

def z575 : W := mkw 0x63f12ffcb11bb330 0x18fc4bff2c46eccc 0xffff3ffff33ff332 0xbfffcffffccffccc

def z576 : W := mkw 0x8f0282404a804888 0x23c0a09012a01222 0x0000000000000000 0x0000000000000000

def z577 : W := mkw 0x00040c1980788150 0x00010306601e2054 0xbd1c3c7f80f883f3 0xaf470f1fe03e20fc

def z578 : W := mkw 0xaf9682454ae448c9 0x2be5a09152b91232 0x011cc0470cc00ccd 0x40473011c3300333

def z579 : W := mkw 0x8400008013805aa8 0x2100002004e016aa 0xde030380f3c0ffff 0xf780c0e03cf03fff

def z580 : W := mkw 0x17dbf4000296ec00 0x85f6fd0000a5bb00 0x52e3fc000307fc00 0x14b8ff0000c1ff00

def z581 : W := mkw 0x63f12ffcb39fb3b1 0x18fc4bff2ce7ecec 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z582 : W := mkw 0x179ed40002f4cc00 0x85e7b50000bd3300 0xb51cfc0000f88c00 0x2d473f00003e2300

def z583 : W := mkw 0x000c581b84680140 0x00031606e11a0050 0xbd1cfc7f8cf803c3 0x2f473f1fe33e00f0

def z584 : W := mkw 0x00085c1284108414 0x00021704a1042105 0xb91cfc7f8c008c3c 0xee473f1fe300230f

def z585 : W := mkw 0x179ed00306e44c44 0x85e7b400c1b91311 0x011cc0470cc00ccd 0x40473011c3300333

def z586 : W := mkw 0x3bfffb77ec600444 0x4efffeddfb180111 0xfbfffffffcc00ccd 0x7effffffff300333

def z587 : W := mkw 0x8f0ed2434ee04ccc 0x23c3b490d3b81333 0x011cc0470cc00ccd 0x40473011c3300333

def z588 : W := mkw 0x109c500000640400 0x8427140000190100 0x001c000000000000 0x0007000000000000

def z589 : W := mkw 0x3bffff76ec708400 0x4effffddbb1c2100 0xfffffffffcf88c00 0x3fffffffff3e2300

def z590 : W := mkw 0x2094000500640041 0x0825000140190010 0x001c000700000000 0x00070001c0000000

def z591 : W := mkw 0x30fd752d007fa541 0x8c3f5d4b401fe950 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z592 : W := mkw 0x8f0282c04b804a88 0x23c0a0b012e012a2 0xcf00c3c00fc00fcf 0x73c030f003f003f3

def z593 : W := mkw 0x4041200030023020 0x101048000c008c08 0x0003000070007000 0x0000c0001c001c00

def z594 : W := mkw 0x23b4036402e40000 0x08ed00d900b90000 0xeffc03ff03ff0000 0x3bff00ffc0ffc000

def z595 : W := mkw 0x544bfc10b012fc30 0x9512ff042c04bf0c 0x1003fc00f000fc30 0x8400ff003c003f0c

def z596 : W := mkw 0x8f0adad2df805aa8 0x23c2b6b4b7e016aa 0xff1fffffffc0ffff 0xffc7fffffff03fff

def z597 : W := mkw 0x379ed24502e44cc1 0x8de7b49140b91330 0x011cc04700c00cc1 0x00473011c0300330

def z598 : W := mkw 0x00612930a0000000 0x00184a4c28000000 0x20e03c3800000000 0x08380f0e00000000

def z599 : W := mkw 0x40612d38a01ba110 0x10184b4e2806e844 0xfae33fb8f03f0000 0x3eb8cfee3c0fc000

def z600 : W := mkw 0x7bfffffffd7bb774 0x5effffffff5eeddd 0xffffffffffffffff 0xffffffffffffffff

def z601 : W := mkw 0x140ad00000004c00 0x8502b40000001300 0x0000c00000000c00 0x0000300000000300

def z602 : W := mkw 0x0402800000004800 0x0100a00000001200 0x1003c0000000fc00 0x0400f00000003f00

def z603 : W := mkw 0x9fdbf2c05b805aa8 0x27f6fcb016e016aa 0xffffffc0ffc0ffff 0xfffffff03ff03fff

def z604 : W := mkw 0x4404048813ffff30 0x9101012204ffffcc 0x0400000003ffff32 0x8100000000ffffcc

def z605 : W := mkw 0x3bffff76ec76a400 0xceffffddbb1da900 0xfbfffffffc3f0000 0x3effffffff0fc000

def z606 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x1400fc008cf88fff 0xc5003f00233e23ff

def z607 : W := mkw 0x000c540b04788554 0x00031502c11e2155 0x051cc0470cf88fff 0xc1473011c33e23ff

def z608 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0xb91cfc7f8c380000 0x2e473f1fe30e0000

def z609 : W := mkw 0x63b40bfdb3ed13f1 0x18ed02ff6cfb44fc 0xeffc03fff3ff03f3 0xbbff00fffcffc0fc

def z610 : W := mkw 0x232003ed038903c1 0x08c800fb40e240f0 0xcf0003ff03c003c3 0x33c000ffc0f000f0

def z611 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x4a0303c0ff0073ff 0xd280c0f03fc01cff

def z612 : W := mkw 0x0000000900080154 0x0000000240020055 0x00000000000003ff 0xc0000000000000ff

def z613 : W := mkw 0x179ed00002e44c00 0x85e7b40000b91300 0xe7fcc00003ff0c00 0x39ff300000ffc300

def z614 : W := mkw 0x43612ff8b39bb3b0 0x10d84bfe2ce6ecec 0xffe33ff8f3fff3f3 0xbff8cffe3cfffcfc

def z615 : W := mkw 0x63f52ffda3ffa3d1 0x18fd4bff68ffe8f4 0xeffc3fff03ff03c3 0x3bff0fffc0ffc0f0

def z616 : W := mkw 0x40412c10b012b030 0x10104b042c04ac0c 0xf6e33c00f33ff030 0xbdb8cf003ccffc0c

def z617 : W := mkw 0xafbedfffdffddffd 0x2befb7fff7ff77ff 0xffffffffffffffff 0xffffffffffffffff

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000c0008c008c3c 0xc40030002300230f

def z619 : W := mkw 0x00085c1a84188514 0x00021706a1062145 0xbc00fc388c388f3e 0xef003f0e230e23cf

def z620 : W := mkw 0x7bfbff76fc12b030 0x5efeffddbf04ac0c 0xfbfffffffc00f030 0xbeffffffff003c0c

def z621 : W := mkw 0xafb283e45b855aa9 0x2beca0f916e156aa 0xdfe3c3c0ffc7ffff 0xf7f8f0f03ff1ffff

def z622 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0x18033fb8f000f332 0x8600cfee3c003ccc

def z623 : W := mkw 0x57dffc10b2f6fc30 0x95f7ff042cbdbf0c 0xf7fffc00f3fffc30 0xbdffff003cffff0c

def z624 : W := mkw 0x2390024402840081 0x08e4009100a10020 0x0000000000000000 0x0000000000000000

def z625 : W := mkw 0x0004081b84680154 0x00010206e11a0055 0xad1c007f8cf803ff 0xeb47001fe33e00ff

def z626 : W := mkw 0x070edc1b86f8cd54 0x01c3b706e1be3355 0xff1ffc7f8ff8ffff 0xffc7ff1fe3fe3fff

def z627 : W := mkw 0x30fd793fa46d0141 0x4c3f5e4fe91b4050 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z628 : W := mkw 0x8c0002c05b805aa8 0x230000b016e016aa 0x0c0003c0ffc0ffff 0xc30000f03ff03fff

def z629 : W := mkw 0xfffbfffeff9bfbb8 0x7ffeffffbfe6feee 0xffffffffffffffff 0xffffffffffffffff

def z630 : W := mkw 0x00412c18801aa110 0x00104b062006a844 0xfee33c38833ff332 0xbfb8cf0e20cffccc

def z631 : W := mkw 0x0000008801090300 0x00000022004240c0 0x04000000033f0302 0x0100000000cfc0c0

def z632 : W := mkw 0x17dff6c003f6ee80 0x85f7fdb000fdbba0 0xffffffc003ffffc3 0x3ffffff000fffff0

def z633 : W := mkw 0x3bfbfbf6ef800280 0x4efefefdbbe000a0 0xffffffffffc003c3 0x3ffffffffff000f0

def z634 : W := mkw 0x184ffc1bec788554 0x4613ff06fb1e2155 0xbd1ffc7ffcf88fff 0xef47ff1fff3e23ff

def z635 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0xcf0303c073c073c3 0x33c0c0f01cf01cf0

def z636 : W := mkw 0x7bf3affcf91bb330 0x5efcebff3e46eccc 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z637 : W := mkw 0x00000c1880188110 0x0000030620062044 0xbd00fc788cf88fff 0xef403f1e233e23ff

def z638 : W := mkw 0x57fffdbbb7ffff74 0x95ffff6eedffffdd 0xffffffffffffffff 0xffffffffffffffff

def z639 : W := mkw 0x406121a031033220 0x101848680c40cc88 0xdee30380f307f332 0xb7b8c0e03cc1fccc

def z640 : W := mkw 0x0390000000000000 0x00e4000000000000 0xe3fc000000000000 0x38ff000000000000

def z641 : W := mkw 0x0b0ede5bcc788554 0x02c3b796f31e2155 0xff1ffffffcf88fff 0xffc7ffffff3e23ff

def z642 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0xb51cfc3f00f88c00 0x2d473f0fc03e2300

def z643 : W := mkw 0x400004001012b030 0x100001000404ac0c 0x000000000000f030 0x8000000000003c0c

def z644 : W := mkw 0x144ffc1b847aed54 0x8513ff06e11ebb55 0xbd1ffc7f8cf8ffff 0xef47ff1fe33e3fff

def z645 : W := mkw 0x0008581b84080154 0x00021606e1020055 0xb91cfc7f8c0003ff 0xee473f1fe30000ff

def z646 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xfffffc408fffffff 0xffffff1023ffffff

def z647 : W := mkw 0x08000812ec000000 0x42000204bb000000 0x00000000fc000000 0x000000003f000000

def z648 : W := mkw 0x8800024048000088 0x2200009012000022 0x000000400c0000cd 0x4000001003000033

def z649 : W := mkw 0x17dff48903ffefc1 0x85f7fd2240fffbf0 0xf7fffc0003ffffc3 0x3dffff0000fffff0

def z650 : W := mkw 0x8b0002c05b8012a8 0x22c000b016e004aa 0xcf0003c0ffc003ff 0xf3c000f03ff000ff

def z651 : W := mkw 0x000c540304708444 0x00031500c11c2111 0xb51cfc470cf88ccd 0x6d473f11c33e2333

def z652 : W := mkw 0x17dbf4000012ec00 0x85f6fd000004bb00 0xf3fffc000000fc00 0x3cffff0000003f00

def z653 : W := mkw 0x406121a8310b3320 0x1018486a0c42ccc8 0xeee303b8733f7302 0x3bb8c0ee1ccfdcc0

def z654 : W := mkw 0xafb283e45b855aa9 0x2beca0f916e156aa 0x42e3038073077000 0x10b8c0e01cc1dc00

def z655 : W := mkw 0x00000c1880188110 0x0000030620062044 0x20003c3800380000 0x08000f0e000e0000

def z656 : W := mkw 0x8404048013f6fea8 0xa101012004fdbfaa 0x0400000003ffffff 0xc100000000ffffff

def z657 : W := mkw 0x13dd740002f6a400 0x84f75d0000bda900 0xe7fc3c0003ff0000 0x39ff0f0000ffc000

def z658 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0x21fcfc7f0c000000 0x087f3f1fc3000000

def z659 : W := mkw 0x280002464c000000 0x4a00009193000000 0x000000470c000000 0x00000011c3000000

def z660 : W := mkw 0x8f0282405a8058a8 0x23c0a09016a0162a 0x1103c040fcc0fcfd 0xc440f0103f303f3f

def z661 : W := mkw 0x33fff3ed03ed03c1 0x0cfffcfb40fb40f0 0xffffffff03ff03c3 0x3fffffffc0ffc0f0

def z662 : W := mkw 0x23f52bfda3ed03c1 0x08fd4aff68fb40f0 0xffff3ffff3ff03c3 0x3fffcffffcffc0f0

def z663 : W := mkw 0x40612db0b113b230 0x10184b6c2c44ec8c 0x52e33f80f307f030 0x94b8cfe03cc1fc0c

def z664 : W := mkw 0x0041200000022000 0x0010480000008800 0x42e3000003077000 0x10b8c00000c1dc00

def z665 : W := mkw 0x406125a8311bb330 0x1018496a0c46eccc 0x46e30380733ff332 0x91b8c0e01ccffccc

def z666 : W := mkw 0x00612d38a0188110 0x00184b4e28062044 0xfee33fb8f0388332 0xbfb8cfee3c0e20cc

def z667 : W := mkw 0x23b403e403e50281 0x08ed00f900f940a0 0xe7fc038003ff0000 0x39ff00e000ffc000

def z668 : W := mkw 0x3b92824448000000 0x4ee4a09112000000 0x0000000000000000 0x0000000000000000

def z669 : W := mkw 0x0004040900788554 0x00010102401e2155 0x9d00c0408cf88fff 0xe7403010233e23ff

def z670 : W := mkw 0x57f3adb8b39ffb30 0x95fceb6e2ce7fecc 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z671 : W := mkw 0x53fbfdb8b11bb330 0x14feff6e2c46eccc 0xffffffb8f33ff332 0xbfffffee3ccffccc

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0xe6e00000033f0000 0x39b8000000cfc000

def z673 : W := mkw 0x8400000002804888 0x2100000000a01222 0x0000000000c00ccd 0x4000000000300333

def z674 : W := mkw 0x0004000000600000 0x0001000000180000 0xa51c000000f80000 0x29470000003e0000

def z675 : W := mkw 0x80000080110012a8 0x20000020044004aa 0x00000000000003ff 0xc0000000000000ff

def z676 : W := mkw 0x0004008903ed03c1 0x0001002240fb40f0 0xad1c007f03ff03c3 0x2b47001fc0ffc0f0

def z677 : W := mkw 0x88000adbdd0813fc 0x220002b6f74204ff 0x080003fffc0003ff 0xc20000ffff0000ff

def z678 : W := mkw 0x0008500204000404 0x0002140081000101 0x0000c0000c000c0c 0x4000300003000303

def z679 : W := mkw 0x8f0686c95bf8dffc 0x23c1a1b256fe37ff 0xdf03c3c0fff8ffff 0xf7c0f0f03ffe3fff

def z680 : W := mkw 0x7bfbfbf6fd033220 0x5efefefdbf40cc88 0xfbffffffff077000 0x3effffffffc1dc00

def z681 : W := mkw 0x000c540900788540 0x00031502401e2150 0xbd1cfc7f00f88fc3 0x2f473f1fc03e23f0

def z682 : W := mkw 0x20000245000000c1 0x0800009140000030 0x00000047000000c1 0x00000011c0000030

def z683 : W := mkw 0x9f9ed2c05be45ea8 0xa7e7b4b016f917aa 0xdf1fc3c0ffc0ffff 0xf7c7f0f03ff03fff

def z684 : W := mkw 0xafb283e45b805aa8 0x2beca0f916e016aa 0xffffc3ffffc0ffff 0xfffff0fffff03fff

def z685 : W := mkw 0x17dffc1882feed10 0x85f7ff0620bfbb44 0xfffffc3883ffff32 0xbfffff0e20ffffcc

def z686 : W := mkw 0x23bc57ed03fd87c1 0x08ef15fb40ff61f0 0xfffcffff03ff8fc3 0x3fff3fffc0ffe3f0

def z687 : W := mkw 0x0000000000000000 0x0000000000000000 0x9c00000080008332 0xa7000000200020cc

def z688 : W := mkw 0xaf2283ed5b895be9 0x2bc8a0fb56e256fa 0xdf03c3ffffc0ffff 0xf7c0f0fffff03fff

def z689 : W := mkw 0x0f0282404a804800 0x03c0a09012a01200 0xdf03c3c0ffc0fc00 0x37c0f0f03ff03f00

def z690 : W := mkw 0x239402cd03ed03c1 0x08e500b340fb40f0 0x051c004703ff03c3 0x01470011c0ffc0f0

def z691 : W := mkw 0x000002c001000280 0x000000b0004000a0 0x080003c0000003c3 0x020000f0000000f0

def z692 : W := mkw 0x0008500000000000 0x0002140000000000 0xb11cfc0000000000 0x2c473f0000000000

def z693 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0x52e3ff80fc000000 0x14b8ffe03f000000

def z694 : W := mkw 0x0004040900788554 0x00010102401e2155 0x0000000000380000 0x00000000000e0000

def z695 : W := mkw 0x8c02800058005828 0x2300a0001600160a 0x9d03c040fcc0ffff 0xe740f0103f303fff

def z696 : W := mkw 0x37fffd36a6f6ec00 0xcdffff4da9bdbb00 0xf7fffc3f03fffc00 0x3dffff0fc0ffff00

def z697 : W := mkw 0x17dff40902feed40 0x85f7fd0240bfbb50 0xfffffc7f03ffffc3 0x3fffff1fc0fffff0

def z698 : W := mkw 0x8f028adbdf885bfc 0x23c0a2b6f7e216ff 0xdf03c3ffffc0ffff 0xf7c0f0fffff03fff

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100c0400cc00ccd 0x4040301003300333

def z700 : W := mkw 0x406d7dbbb57bb774 0x101b5f6eed5eeddd 0xfeff3fbff33ff332 0xbfbfcfeffccffccc

def z701 : W := mkw 0x3b9ed2474c600444 0x4ee7b491d3180111 0x011cc0470cc00ccd 0x40473011c3300333

def z702 : W := mkw 0x0061212020000000 0x0018484808000000 0x42e3038070000000 0x10b8c0e01c000000

def z703 : W := mkw 0x13dffc1b84788554 0x04f7ff06e11e2155 0xfffffc7f8cf88fff 0xffffff1fe33e23ff

def z704 : W := mkw 0x386bfb76ec000000 0x4e1afeddbb000000 0x1803fffffc000000 0x0600ffffff000000

def z705 : W := mkw 0x880c5edbdd7897fc 0x220317b6f75e25ff 0xbd1cfffffcf88fff 0xef473fffff3e23ff

def z706 : W := mkw 0x40612d38a01ba110 0x10184b4e2806e844 0xf6e33c38033ff000 0x3db8cf0e00cffc00

def z707 : W := mkw 0x3bf7a76d68788554 0x4efde9db5a1e2155 0x46e3038070f88fff 0xd1b8c0e01c3e23ff

def z708 : W := mkw 0xacb6812d586d5969 0x2b2da04b561b565a 0x30ffc03ffc3ffc3c 0xcc3ff00fff0fff0f

def z709 : W := mkw 0x50fd7d3ba47fa554 0x943f5f4ee91fe955 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z710 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0x191ffffffc000000 0x0647ffffff000000

def z711 : W := mkw 0x20b401ad016d0341 0x082d006b405b40d0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z712 : W := mkw 0x00940009006c0140 0x00250002401b0050 0x20fc003f003f0000 0x083f000fc00fc000

def z713 : W := mkw 0x184ff89befed03c1 0x4613fe26fbfb40f0 0x1403fc00ffff03c3 0x0500ff003fffc0f0

def z714 : W := mkw 0x406d71a335633664 0x101b5c68cd58cd99 0x43ffc3c77fc77ccd 0x50fff0f1dff1df33

def z715 : W := mkw 0x50497c12a412a010 0x54125f04a904a804 0x00003c0000000000 0x00000f0000000000

def z716 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0x72fffc00033ffc00 0x1cbfff0000cfff00

def z717 : W := mkw 0x14dd740002f6ec00 0x85375d0000bdbb00 0x20fc3c00033f7000 0x083f0f0000cfdc00

def z718 : W := mkw 0x3f9ed2474ee44c44 0xcfe7b491d3b91311 0x011cc0470cc00ccd 0x40473011c3300333

def z719 : W := mkw 0x98dd76c05976b6a8 0xa6375db0165dadaa 0x28fc3fc0fc3f03ff 0xca3f0ff03f0fc0ff

def z720 : W := mkw 0x000c5c1b847d8555 0x00031706e11f6155 0xbd1cfc7f8cff8fff 0xef473f1fe33fe3ff

def z721 : W := mkw 0x3bfbfb76ec000404 0x4efefeddbb000101 0xfbfffffffc000c0c 0x7effffffff000303

def z722 : W := mkw 0x27b683ed13ed5be1 0x09eda0fb44fb56f8 0xffffc3fff3fffff3 0xbffff0fffcfffffc

def z723 : W := mkw 0xfff3a3e47b837aa8 0x7ffce8f91ee0deaa 0x42e3038073077000 0x10b8c0e01cc1dc00

def z724 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0xbdfcc07f8cff8fff 0xef7f301fe33fe3ff

def z725 : W := mkw 0x33fbf936a4000000 0x4cfefe4da9000000 0xfbffffbff0000000 0x3effffeffc000000

def z726 : W := mkw 0x1fdff4006af6ec00 0xc7f7fd001abdbb00 0xf7fffc0073fffc00 0x3dffff001cffff00

def z727 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0x24fc003f00ff03c3 0x093f000fc03fc0f0

def z728 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x5603c380ffc0ffff 0xd580f0e03ff03fff

def z729 : W := mkw 0x63d52e55b2f6b0f1 0x18f54b956cbdac3c 0x111f3c47f0c0f0f1 0x8447cf11fc303c3c

def z730 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xf7fffc008ffffc3c 0xfdffff0023ffff0f

def z731 : W := mkw 0x2bb683ed4bed03c1 0x0aeda0fb52fb40f0 0xffffc3ffffff8fff 0xfffff0ffffffe3ff

def z732 : W := mkw 0x23b003ec038d0381 0x08ec00fb00e340e0 0xeffc03ff033f0302 0x3bff00ffc0cfc0c0

def z733 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0x9d00c3f8fcc08fff 0xe74030fe3f3023ff

def z734 : W := mkw 0x104bf4000012a000 0x0412fd000004a800 0xf6e3fc00033ff000 0x3db8ff0000cffc00

def z735 : W := mkw 0x1b4bfa52ec000000 0x46d2fe94bb000000 0xfb1ffffffc000000 0x3ec7ffffff000000

def z736 : W := mkw 0x17dff40102f6ecc1 0x85f7fd0040bdbb30 0xf7fffc0003fffcc1 0x3dffff0000ffff30

def z737 : W := mkw 0x27b683ed03ed4bc1 0x09eda0fb40fb52f0 0xefff03ff03ff73c3 0x3bffc0ffc0ffdcf0

def z738 : W := mkw 0x23b401ad03ed0341 0x08ed006b40fb40d0 0xeffc03bf03ff0302 0x3bff00efc0ffc0c0

def z739 : W := mkw 0x0702808013805a20 0x01c0a02004e01688 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z740 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xf6e33fb8733ff000 0x3db8cfee1ccffc00

def z741 : W := mkw 0x38fbf936ec000000 0x4e3efe4dbb000000 0xfaffffbffc000000 0x3ebfffefff000000

def z742 : W := mkw 0x17dff00002e44800 0x05f7fc0000b91200 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z743 : W := mkw 0x8c0280805b805aa8 0x2300a02016e016aa 0xde03c380ffc0ffff 0xf780f0e03ff03fff

def z744 : W := mkw 0x20b401ad016d0341 0x082d006b405b40d0 0x28fc03bf003f0302 0x0a3f00efc00fc0c0

def z745 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xfffffc0083ffff32 0xbfffff0020ffffcc

def z746 : W := mkw 0x00d524000076a000 0x00354900001da800 0xf6ff3c00033ff000 0x3dbfcf0000cffc00

def z747 : W := mkw 0x17dff00002e66800 0x85f7fc0000b99a00 0xf7fffc0003ff7000 0x3dffff0000ffdc00

def z748 : W := mkw 0x9f4bfed2df92febc 0xa7d2ffb4b7e4bfaf 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z749 : W := mkw 0xc0612db8b11bb3b8 0x30184b6e2c46ecee 0xfee33fb8f33ff3ff 0xffb8cfee3ccffcff

def z750 : W := mkw 0x0b0282c059001220 0x02c0a0b016400488 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z751 : W := mkw 0x0394000002e40000 0x00e5000000b90000 0xeffc007f03ff0000 0x3bff001fc0ffc000

def z752 : W := mkw 0x20b403ed016d03c1 0x082d00fb405b40f0 0x20fc03bf003f0000 0x083f00efc00fc000

def z753 : W := mkw 0xbffbfb76ee804888 0x6ffefeddbba01222 0xffffffffffc0fccd 0x7ffffffffff03f33

def z754 : W := mkw 0xbf9ed2474ee448c9 0x6fe7b491d3b91232 0x011cc0470cc00ccd 0x40473011c3300333

def z755 : W := mkw 0x60612dbdb11bb371 0x18184b6f6c46ecdc 0xfee33fbff33ff332 0xbfb8cfeffccffccc

def z756 : W := mkw 0x23b403ed03ed03d5 0x08ed00fb40fb40f5 0xeffc03ff03ff03ff 0xfbff00ffc0ffc0ff

def z757 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0x63fffc0003ff7c00 0x18ffff0000ffdf00

def z758 : W := mkw 0x7b9ad6ce5d1bb330 0x5ee6b5b39746eccc 0x051cc0470f3ff332 0x81473011c3cffccc

def z759 : W := mkw 0xb4f979b6b7805aa8 0x6d3e5e6dade016aa 0x24fc3c3f03c0ffff 0xc93f0f0fc0f03fff

def z760 : W := mkw 0x3bbadb76ec000000 0x4eeeb6ddbb000000 0xb91cfffffc000000 0x2e473fffff000000

def z761 : W := mkw 0x40040489117fb371 0x10010122445fecdc 0x04000000033ff332 0x8100000000cffccc

def z762 : W := mkw 0x406129b8b10b3320 0x10184a6e2c42ccc8 0xfee33fb8f33f7302 0x3fb8cfee3ccfdcc0

def z763 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0x29fc03ff00ff03c3 0x0a7f00ffc03fc0f0

def z764 : W := mkw 0x23b85ff687958695 0x08ee17fda1e561a5 0x52e0ff808f078c3c 0xd4b83fe023c1e30f

def z765 : W := mkw 0x17d3a4000296e800 0x85f4e90000a5ba00 0xf7e3fc0003fffc00 0x3df8ff0000ffff00

def z766 : W := mkw 0x3ffbfb76ec004800 0x4ffefeddbb001200 0xfbfffffffc00fc00 0x3effffffff003f00

def z767 : W := mkw 0x17d3a81b868e6954 0x85f4ea06e1a39a55 0x4ae3007f8f0773ff 0xd2b8c01fe3c1dcff

def z768 : W := mkw 0xafb683ed4bed4bc9 0x2beda0fb52fb52f2 0xffffc3ff0fffffcf 0x7ffff0ffc3fffff3

def z769 : W := mkw 0x17dff40102f6ec40 0x85f7fd0040bdbb10 0xf7fffc4703fffcc1 0x3dffff11c0ffff30

def z770 : W := mkw 0x9fdff6404af6ec88 0xa7f7fd9012bdbb22 0xffffffc0fffffccd 0x7ffffff03fffff33

def z771 : W := mkw 0x40612dbab51bb330 0x10184b6ead46eccc 0xfee33fffff3ff332 0xbfb8cfffffcffccc

def z772 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xffe3fff8ff3ff332 0xbff8fffe3fcffccc

def z773 : W := mkw 0xafb683ed4bed4bc9 0x2beda0fb52fb52f2 0xfffcc3ff8fff8fff 0xffff30ffe3ffe3ff

def z774 : W := mkw 0x8f0ededbdff8dffc 0x23c3b7b6f7fe37ff 0x621f3fbf73387000 0x1887cfefdcce1c00

def z775 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x191cfc7f8cc08fff 0xc6473f1fe33023ff

def z776 : W := mkw 0x14dff4000076ec00 0x8537fd00001dbb00 0xf6fffc00033ffc00 0x3dbfff0000cfff00

def z777 : W := mkw 0x17dff64002f6ec80 0x85f7fd9000bdbb20 0xf7fffc4003fffcc1 0x3dffff1000ffff30

def z778 : W := mkw 0xbff3a3e47b855aa9 0x6ffce8f91ee156aa 0x42e3038073077000 0x10b8c0e01cc1dc00

def z779 : W := mkw 0xa8200bffdd0913fd 0x2a0802fff74244ff 0x080003fffc0003ff 0xc20000ffff0000ff

def z780 : W := mkw 0x0f0282404a804800 0x03c0a09012a01200 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z781 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0x21fc007f00ff00c1 0x087f001fc03fc030

def z782 : W := mkw 0x3bfbf36448000000 0x0efefcd912000000 0xfbfffffffc000000 0x3effffffff000000

def z783 : W := mkw 0xa8200bfffd0913e9 0x6a0802ffff4244fa 0x080003fffc0003ff 0xc20000ffff0000ff

def z784 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0x6afc03ff033f03c3 0x1abf00ffc0cfc0f0

def z785 : W := mkw 0x13fbf932a4000000 0x04fefe4ca9000000 0xfbfffffffc000000 0x3effffffff000000

def z786 : W := mkw 0x40040489117bb774 0x10010122445eeddd 0x04000000033ff332 0x8100000000cffccc

def z787 : W := mkw 0x23b4036400640000 0x08ed00d900190000 0xebfc03ff003f0000 0x3aff00ffc00fc000

def z788 : W := mkw 0x602009beb5091330 0x5808026fad4244cc 0x080003bff0000332 0x820000effc0000cc

def z789 : W := mkw 0x23b403ed016d03c1 0x08ed00fb405b40f0 0xebfc03ff003f03c3 0x3aff00ffc00fc0f0

def z790 : W := mkw 0x23b403ec03ed0300 0x08ed00fb00fb40c0 0xeffc03ff03ff0302 0x3bff00ffc0ffc0c0

def z791 : W := mkw 0x1fdff4004af6ec00 0x87f7fd0012bdbb00 0xf7fffc00fffffc00 0x3dffff003fffff00

def z792 : W := mkw 0xeff3a3e47b877aa9 0x3bfce8f91ee1deaa 0x42e3038073077000 0x10b8c0e01cc1dc00

def z793 : W := mkw 0x9f4bfed2ff92fea8 0xe7d2ffb4bfe4bfaa 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z794 : W := mkw 0x37dff64402f6ec81 0x8df7fd9100bdbb20 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z795 : W := mkw 0x23b403e403e40280 0x08ed00f900f900a0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z796 : W := mkw 0x0b06864948788554 0x02c1a192521e2155 0xdf03c3c0fcf88fff 0xf7c0f0f03f3e23ff

def z797 : W := mkw 0x20b401ad03ed03c1 0x082d006b40fb40f0 0x20fc003f033f0000 0x083f000fc0cfc000

def z798 : W := mkw 0x8f0282c05b855aa9 0x23c0a0b016e156aa 0xdf03c3c0ffc7ffff 0xf7c0f0f03ff1ffff

def z799 : W := mkw 0x9fdff6404af6ec88 0xa7f7fd9012bdbb22 0xfffffc408fffffff 0xffffff1023ffffff

def z800 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xefff03ffffff73ff 0xfbffc0ffffffdcff

def z801 : W := mkw 0x544bfc12b412fc34 0x9512ff04ad04bf0d 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z802 : W := mkw 0x23b4012d02ed0141 0x08ed004b40bb4050 0x21fc003f00ff0000 0x087f000fc03fc000

def z803 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0x72ffffbffc000000 0x1cbfffefff000000

def z804 : W := mkw 0x03d124000296a000 0x00f4490000a5a800 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z805 : W := mkw 0x004124000012a000 0x001049000004a800 0xf7e3fc0003fffc00 0x3df8ff0000ffff00

def z806 : W := mkw 0x004124801112b220 0x001049200444ac88 0xf6e33f80733ff000 0x3db8cfe01ccffc00

def z807 : W := mkw 0x1f9ed2404ae44c00 0x87e7b49012b91300 0x011cc0400cc00c00 0x0047301003300300

def z808 : W := mkw 0x2bb683ed4bed03c1 0x0aeda0fb52fb40f0 0xeffcc3ff0fff03c3 0x3bff30ffc3ffc0f0

def z809 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xfee3ffb8ff3fff3e 0xffb8ffee3fcfffcf

def z810 : W := mkw 0x63b403ed13ed13f1 0x18ed00fb44fb44fc 0xeffc03ff03ff03f3 0xbbff00ffc0ffc0fc

def z811 : W := mkw 0xa7b403ed03ed4bc9 0x29ed00fb40fb52f2 0xeffc03ff03ff0fcf 0x7bff00ffc0ffc3f3

def z812 : W := mkw 0x074ff40002f2ec00 0x01d3fd0000bcbb00 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z813 : W := mkw 0x40497c12a412a414 0x10125f04a904a905 0x00003c0000000000 0x00000f0000000000

def z814 : W := mkw 0x23b683ed03ed03c1 0x08eda0fb40fb40f0 0xffffc3ff03ff03c3 0x3ffff0ffc0ffc0f0

def z815 : W := mkw 0x004124000012a000 0x001049000004a800 0xfee33f80f33ff000 0x3fb8cfe03ccffc00

def z816 : W := mkw 0x3ffbfb76ee804800 0x4ffefeddbba01200 0xfbfffffffcc00c00 0x3effffffff300300

def z817 : W := mkw 0x23b4036d02ed01c1 0x08ed00db40bb4070 0xebfc03ff00ff00c1 0x3aff00ffc03fc030

def z818 : W := mkw 0xbffbfb76ee804888 0x6ffefeddbba01222 0xfbfffffffc000000 0x3effffffff000000

def z819 : W := mkw 0x10d124000016a000 0x843449000005a800 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z820 : W := mkw 0x004124000012a000 0x001049000004a800 0x24e03c00033ff000 0x09380f0000cffc00

def z821 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xe7fc03bf03ff0000 0x39ff00efc0ffc000

def z822 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0x29fcfffffc000000 0x0a7f3fffff000000

def z823 : W := mkw 0x1fdff4024ef6ec00 0xc7f7fd0093bdbb00 0xf7fffc000ffffc00 0x3dffff0003ffff00

def z824 : W := mkw 0x17d7a40002f6e800 0x85f5e90000bdba00 0xf7ff3c0003fff000 0x3dffcf0000fffc00

def z825 : W := mkw 0x17dff40306f6ec44 0x85f7fd00c1bdbb11 0xf7fffc0703fffc00 0x3dffff01c0ffff00

def z826 : W := mkw 0x8f9282c05b845aa8 0x23e4a0b016e116aa 0xdfe3c3c0ffc7ffff 0xf7f8f0f03ff1ffff

def z827 : W := mkw 0xbff3a3e45b877aa9 0xaffce8f916e1deaa 0x42e3038073077000 0x10b8c0e01cc1dc00

def z828 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xeffcc3ffffff0fff 0xfbff30ffffffc3ff

def z829 : W := mkw 0xa7b403ed13ed5be9 0x29ed00fb44fb56fa 0xffff03fff3ffffff 0xffffc0fffcffffff

def z830 : W := mkw 0x40612db9b11bb370 0x10184b6e6c46ecdc 0xfee33ffff33ff3f3 0xbfb8cffffccffcfc

def z831 : W := mkw 0x406125a8311bb320 0x1018496a0c46ecc8 0xfee33fb8733ff302 0x3fb8cfee1ccffcc0

def z832 : W := mkw 0x13d3a4000012a000 0x04f4e9000004a800 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z833 : W := mkw 0x17dbf4000296ec00 0x85f6fd0000a5bb00 0xf6e3fc00033ffc00 0x3db8ff0000cfff00

def z834 : W := mkw 0xcf63af78ea9be998 0x33d8ebde3aa6fa66 0x21e0fc780cff0ccd 0x48783f1e033fc333

def z835 : W := mkw 0x346bf7ed011befc1 0x8d1afdfb4046fbf0 0x1803ffff0000ffc3 0x0600ffffc0003ff0

def z836 : W := mkw 0x3ffbfb76ee866800 0xcffefeddbba19a00 0xffffffffffc7fc00 0x3ffffffffff1ff00

def z837 : W := mkw 0x10497c12a412a400 0xc4125f04a904a900 0x00003c0000000000 0x00000f0000000000

def z838 : W := mkw 0x174bfc128692ec14 0x85d2ff04a1a4bb05 0xdf03fc408fc0ffff 0xf7c0ff1023f03fff

def z839 : W := mkw 0x030002c0138012a0 0x00c000b004e004a8 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z840 : W := mkw 0x60fd7d3fa47fa555 0x183f5f4fe91fe955 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z841 : W := mkw 0x3bfbfb76ee840081 0x4efefeddbba10020 0xfbfffffffc000000 0x3effffffff000000

def z842 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfffffffffcc08c00 0x3fffffffff302300

def z843 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0x72e33fb8f33ff030 0x9cb8cfee3ccffc0c

def z844 : W := mkw 0x23b403ed03ed07c5 0x08ed00fb40fb41f1 0xeffc03ff03ff0fcf 0x7bff00ffc0ffc3f3

def z845 : W := mkw 0x9c4bfc12dc12fc3c 0xa712ff04b704bf0f 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z846 : W := mkw 0x40040489117bb370 0x10010122445eecdc 0x0400000003fff3f3 0x8100000000fffcfc

def z847 : W := mkw 0x23b403ed13ed13e1 0x08ed00fb44fb44f8 0xeffc03ff03fff3f3 0xbbff00ffc0fffcfc

def z848 : W := mkw 0xafb683ed4bed4bc9 0x2beda0fb52fb52f2 0xffffc3ffffff0fcf 0x7ffff0ffffffc3f3

def z849 : W := mkw 0x40612db8b11bb734 0x10184b6e2c46edcd 0xfee33fb8f33fff3e 0xffb8cfee3ccfffcf

def z850 : W := mkw 0x402009bbb5091374 0x1008026eed4244dd 0x080003bff0000332 0x820000effc0000cc

def z851 : W := mkw 0x3bf97b76ec000000 0x4efe5eddbb000000 0xebfc3ffffc000000 0x3aff0fffff000000

def z852 : W := mkw 0x002401a911691360 0x0009006a445a44d8 0xffffc3ffffffffff 0xfffff0ffffffffff

def z853 : W := mkw 0x23b403ed13ed13e1 0x08ed00fb44fb44f8 0xeffc03fff3ff03f3 0xbbff00fffcffc0fc

def z854 : W := mkw 0x23b4036d02ed01c1 0x08ed00db40bb4070 0xadfc007f00ff03c3 0x2b7f001fc03fc0f0

def z855 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x291cfc7f8cf80fff 0xca473f1fe33e03ff

def z856 : W := mkw 0x40412c90b112b230 0x10104b242c44ac8c 0xfee33f80f33ff332 0xbfb8cfe03ccffccc

def z857 : W := mkw 0x3ffbfb76ee804800 0x4ffefeddbba01200 0xfbffffffff007000 0x3effffffffc01c00

def z858 : W := mkw 0xa7b403ed13ed5be9 0x29ed00fb44fb56fa 0xfffcc3ff8fffffff 0xffff30ffe3ffffff

def z859 : W := mkw 0x40497c92b512b634 0x10125f24ad44ad8d 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z860 : W := mkw 0x000c540900788540 0x00031502401e2150 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z861 : W := mkw 0x034124000292a000 0x00d0490000a4a800 0xf7e33c0003fff000 0x3df8cf0000fffc00

def z862 : W := mkw 0x2c240f76eef6ec00 0xcb0903ddbbbdbb00 0x0c0003fffffffc00 0x030000ffffffff00

def z863 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0x251cfc7f0cf88fff 0xc9473f1fc33e23ff

def z864 : W := mkw 0x20b401ad016d0341 0x082d006b405b40d0 0x24fc003f033f0302 0x093f000fc0cfc0c0

def z865 : W := mkw 0xafb683e45be45aa8 0x2beda0f916f916aa 0xffffc3ffffffffff 0xfffff0ffffffffff

def z866 : W := mkw 0x184bfc12ec12a000 0x4612ff04bb04a800 0x1003fc00fc00f000 0x0400ff003f003c00

def z867 : W := mkw 0x00200db891199330 0x0008036e244664cc 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z868 : W := mkw 0x38f97b76ec000000 0x4e3e5eddbb000000 0x20fc3fbf70000000 0x083f0fefdc000000

def z869 : W := mkw 0x004524000072a000 0x00114900001ca800 0xf7ff3c0003fff000 0x3dffcf0000fffc00

def z870 : W := mkw 0x00612930a0000000 0x00184a4c28000000 0xfbff3ffff0000000 0x3effcffffc000000

def z871 : W := mkw 0x044d740002f6ec00 0x81135d0000bdbb00 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z872 : W := mkw 0x60200bfcb1091330 0x180802ff2c4244cc 0x080003fff0000332 0x820000fffc0000cc

def z873 : W := mkw 0xc8200bf8f90913b8 0x320802fe3e4244ee 0x080003b8f0000332 0x820000ee3c0000cc

def z874 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xffffffffff3f0000 0x3fffffffffcfc000

def z875 : W := mkw 0x27b6812d02ed4941 0x09eda04b40bb5250 0xf7ffc03f03fffc00 0x3dfff00fc0ffff00

def z876 : W := mkw 0x57bed9b8b3ed5f30 0x95efb66e2cfb57cc 0x091cc3b8f0c00f32 0x824730ee3c3003cc

def z877 : W := mkw 0x14dff40002f6ec00 0x8537fd0000bdbb00 0x34fffc0003fffc00 0x0d3fff0000ffff00

def z878 : W := mkw 0x20b403ed016d03c1 0x082d00fb405b40f0 0xeefc03ff033f03c3 0x3bbf00ffc0cfc0f0

def z879 : W := mkw 0x3bfbfb76ee840000 0x4efefeddbba10000 0xfbffffffff070000 0x3effffffffc1c000

def z880 : W := mkw 0x8404048913fddffd 0x2101012244ff77ff 0x0400000003ffffff 0xc100000000ffffff

def z881 : W := mkw 0xc02009b8b10913b8 0x3008026e2c4244ee 0x080003b8f00003ff 0xc20000ee3c0000ff

def z882 : W := mkw 0x004974000012a400 0x00125d000004a900 0xf6e3fc00033ffc00 0x3db8ff0000cfff00

def z883 : W := mkw 0x00285932a4000000 0x000a164ca9000000 0xb91cfffffc000000 0x2e473fffff000000

def z884 : W := mkw 0x880002c0590012a8 0x220000b0164004aa 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z885 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xffffffffff00f000 0x3fffffffffc03c00

def z886 : W := mkw 0x3fdff6474ef6ecc1 0xcff7fd91d3bdbb30 0xf7fffc470ffffcc1 0x3dffff11c3ffff30

def z887 : W := mkw 0x40612dbbb51bb374 0x10184b6eed46ecdd 0xfee33fbff33ff332 0xbfb8cfeffccffccc

def z888 : W := mkw 0x10dd74000076a400 0x84375d00001da900 0x62ff3c00033f7000 0x18bfcf0000cfdc00

def z889 : W := mkw 0x002401a901690340 0x0009006a405a40d0 0xeefc03bf033f0302 0x3bbf00efc0cfc0c0

def z890 : W := mkw 0x3bf3ab74e8000000 0x4efceadd3a000000 0xfbff3ffff0000000 0x3effcffffc000000

def z891 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xfffc03ff83ff83f3 0xbfff00ffe0ffe0fc

def z892 : W := mkw 0x9f9ed2434ee44ccc 0xa7e7b490d3b91333 0x011cc0470cc00ccd 0x40473011c3300333

def z893 : W := mkw 0x032403e903e903c0 0x00c900fa40fa40f0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z894 : W := mkw 0x0004048911789774 0x00010122445e25dd 0x0400000003f8ffff 0xc100000000fe3fff

def z895 : W := mkw 0x406125a8311bb330 0x1018496a0c46eccc 0xf6e33f80733ff332 0xbdb8cfe01ccffccc

def z896 : W := mkw 0x9c4bfc12fc12fc28 0xe712ff04bf04bf0a 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z897 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xeefc03bf033f0302 0x3bbf00efc0cfc0c0

def z898 : W := mkw 0x28285b76ec000000 0x4a0a16ddbb000000 0x281c3ffffc000000 0x0a070fffff000000

def z899 : W := mkw 0x006129b8b1091320 0x00184a6e2c4244c8 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z900 : W := mkw 0x23b0036c00090100 0x08ec00db00024040 0xebfc03ff003f0000 0x3aff00ffc00fc000

def z901 : W := mkw 0x144ff4000072ec00 0x8513fd00001cbb00 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z902 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xf6ff3c00033ff000 0x3dbfcf0000cffc00

def z903 : W := mkw 0x07d5240002f6ec00 0x81f5490000bdbb00 0xf7ff3c0003fffc00 0x3dffcf0000ffff00

def z904 : W := mkw 0x2bb683ed4bed03c1 0x0aeda0fb52fb40f0 0xefff03ff73ff03c3 0x3bffc0ffdcffc0f0

def z905 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0xffe3c3c0ffffffff 0xfff8f0f03fffffff

def z906 : W := mkw 0x0008581284000000 0x00021604a1000000 0xfb1ffffffc000000 0x3ec7ffffff000000

def z907 : W := mkw 0x20b401ad016d0341 0x082d006b405b40d0 0x62fc03bf033f0000 0x18bf00efc0cfc000

def z908 : W := mkw 0x40612d30b012b030 0x10184b4c2c04ac0c 0xfee33fb8f33ff030 0xbfb8cfee3ccffc0c

def z909 : W := mkw 0xbf9ed2464ee44c88 0xefe7b49193b91322 0x011cc0470cc00ccd 0x40473011c3300333

def z910 : W := mkw 0xaf9282c45b845aa9 0x2be4a0b116e116aa 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z911 : W := mkw 0x402c59bbb5691774 0x100b166eed5a45dd 0x091cc3fffcc00fff 0xc24730ffff3003ff

def z912 : W := mkw 0x000c581b84680554 0x00031606e11a0155 0xb91cfc7f8cc00fff 0xee473f1fe33003ff

def z913 : W := mkw 0x23b003ec03890380 0x08ec00fb00e240e0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z914 : W := mkw 0x3bfbfb76ec050001 0x4efefeddbb014000 0xfbfffffffc070000 0x3effffffff01c000

def z915 : W := mkw 0x40497c12a412a414 0x10125f04a904a905 0x1000fc008c008c3c 0xc4003f002300230f

def z916 : W := mkw 0x9fdff6434ef6eccc 0xa7f7fd90d3bdbb33 0xf7fffc470ffffccd 0x7dffff11c3ffff33

def z917 : W := mkw 0x039402c903ec03c0 0x00e500b240fb00f0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z918 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xffff03ff03fff3c3 0x3fffc0ffc0fffcf0

def z919 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0xe6fc003f033f0000 0x39bf000fc0cfc000

def z920 : W := mkw 0x23b0036400000000 0x08ec00d900000000 0xeffc03ff033f0000 0x3bff00ffc0cfc000

def z921 : W := mkw 0x144bfc12a412ec00 0xc512ff04a904bb00 0x1003fc000000fc00 0x0400ff0000003f00

def z922 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xefff03ff73ffffff 0xfbffc0ffdcffffff

def z923 : W := mkw 0x9fdff4004af6ec08 0xa7f7fd0012bdbb02 0xf7fffc000ffffc0c 0x7dffff0003ffff03

def z924 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xfffffc7f03fffc00 0x3fffff1fc0ffff00

def z925 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0x1903c3c0fcc0ffff 0xc640f0f03f303fff

def z926 : W := mkw 0x3ffbfb76ee804800 0x4ffefeddbba01200 0xffffffffffc0ffff 0xfffffffffff03fff

def z927 : W := mkw 0x23b4012d02ed0141 0x08ed004b40bb4050 0xeffc007f03ff03c3 0x3bff001fc0ffc0f0

def z928 : W := mkw 0x006125202012a000 0x001849480804a800 0xf6e33f80733ff000 0x3db8cfe01ccffc00

def z929 : W := mkw 0xbfdff6454af6ecc9 0xaff7fd9152bdbb32 0xf7fffc470ffffccd 0x7dffff11c3ffff33

def z930 : W := mkw 0x0024012900690140 0x0009004a401a4050 0xadfc007f00ff03c3 0x2b7f001fc03fc0f0

def z931 : W := mkw 0x2bbadb76cc000000 0x0aeeb6ddb3000000 0xfbfffffffc000000 0x3effffffff000000

def z932 : W := mkw 0x402009bab5091334 0x1008026ead4244cd 0x080003b8fc00033e 0xc20000ee3f0000cf

def z933 : W := mkw 0x3bfbfb76ee800000 0x4efefeddbba00000 0xffffffffffc00000 0x3ffffffffff00000

def z934 : W := mkw 0x8f43a6404a92e888 0x23d0e99012a4ba22 0xf7e3fc400ffffccd 0x7df8ff1003ffff33

def z935 : W := mkw 0x402009b9b1091374 0x1008026e6c4244dd 0x080003b8f00003ff 0xc20000ee3c0000ff

def z936 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xf7fffc400ffffccd 0x7dffff1003ffff33

def z937 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0xfffcfc7f8fff8fff 0xffff3f1fe3ffe3ff

def z938 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0x28fc007f003f03c3 0x0a3f001fc00fc0f0

def z939 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xe7ff3c0003ff7000 0x39ffcf0000ffdc00

def z940 : W := mkw 0xafb283ec5b895ba8 0x2beca0fb16e256ea 0xffffc3ffffffffff 0xfffff0ffffffffff

def z941 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xeffcc3ff0fff0fcf 0x7bff30ffc3ffc3f3

def z942 : W := mkw 0xcf228bf8fb895bb8 0x33c8a2fe3ee256ee 0x0900c3f8fcc00fff 0xc24030fe3f3003ff

def z943 : W := mkw 0x23b4036d02ed01c1 0x08ed00db40bb4070 0xe7fc007f03ff00c1 0x39ff001fc0ffc030

def z944 : W := mkw 0xc404048913fffbf9 0x3101012244fffefe 0x0400000003ffffff 0xc100000000ffffff

def z945 : W := mkw 0x30f97936a4000000 0x4c3e5e4da9000000 0x62ff3fbf70000000 0x18bfcfefdc000000

def z946 : W := mkw 0x004d74000072a400 0x00135d00001ca900 0xf6ff3c00033ff000 0x3dbfcf0000cffc00

def z947 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xeffcc3ff0fffffff 0xfbff30ffc3ffffff

def z948 : W := mkw 0x2bb683ed5bed13e1 0x0aeda0fb56fb44f8 0xffffc3fffffff3f3 0xbffff0fffffffcfc

def z949 : W := mkw 0x23b403e403e50281 0x08ed00f900f940a0 0xeffc03ff03ff0000 0x3bff00ffc0ffc000

def z950 : W := mkw 0x20b4036d006d01c1 0x082d00db401b4070 0x20fc007f003f00c1 0x083f001fc00fc030

def z951 : W := mkw 0x00940009006c0140 0x00250002401b0050 0xadfc007f00ff03c3 0x2b7f001fc03fc0f0

def z952 : W := mkw 0x2bb283ec59091320 0x0aeca0fb164244c8 0xffffc3ffff3ff332 0xbffff0ffffcffccc

def z953 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xfffffc4003ffffc3 0x3fffff1000fffff0

def z954 : W := mkw 0x584bfc12fc12b434 0x5612ff04bf04ad0d 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z955 : W := mkw 0x68200bfffd0913f1 0x5a0802ffff4244fc 0x080003fffc0003f3 0x820000ffff0000fc

def z956 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0xff1ffc7f8ff8ffff 0xffc7ff1fe3fe3fff

def z957 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xebfc03ff033f0000 0x3aff00ffc0cfc000

def z958 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0x000003b870000000 0x000000ee1c000000

def z959 : W := mkw 0xafb6836d4aed49c9 0x2beda0db52bb5272 0x21fcc07f0cff0ccd 0x487f301fc33fc333

def z960 : W := mkw 0x2394024d02ec01c1 0x08e5009340bb0070 0xeffc007f03ff03c3 0x3bff001fc0ffc0f0

def z961 : W := mkw 0xe8200bfdf90913f9 0x3a0802ff7e4244fe 0x080003fffc0003ff 0xc20000ffff0000ff

def z962 : W := mkw 0x37dff40502f6ec41 0x8df7fd0140bdbb10 0xf7fffc0703fffc00 0x3dffff01c0ffff00

def z963 : W := mkw 0x23b4036d006d0141 0x08ed00db401b4050 0xeffc03ff00ff03c3 0x3bff00ffc03fc0f0

def z964 : W := mkw 0x8f2683e95be95be8 0x23c9a0fa56fa56fa 0xffffc3ffffffffff 0xfffff0ffffffffff

def z965 : W := mkw 0x104974000012a400 0x84125d000004a900 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z966 : W := mkw 0x00085c1a84188110 0x00021706a1062044 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z967 : W := mkw 0x079c540002f6ec00 0x81e7150000bdbb00 0xf7fcfc0003fffc00 0x3dff3f0000ffff00

def z968 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xebff3fff70000000 0x3affcfffdc000000

def z969 : W := mkw 0x174bf4000292ec00 0x85d2fd0000a4bb00 0xf7e3fc0003fffc00 0x3df8ff0000ffff00

def z970 : W := mkw 0x3bfbfb76ec022000 0x4efefeddbb008800 0xfbffffffff077000 0x3effffffffc1dc00

def z971 : W := mkw 0x3bdbf6464c12a000 0x4ef6fd919304a800 0xf7fffc470f3ff000 0x3dffff11c3cffc00

def z972 : W := mkw 0x23b4036d02ed01c1 0x08ed00db40bb4070 0x20fc003f003f0000 0x083f000fc00fc000

def z973 : W := mkw 0x00612db0b112b220 0x00184b6c2c44ac88 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z974 : W := mkw 0x20b4012d02ed0141 0x082d004b40bb4050 0x24fc003f03ff0000 0x093f000fc0ffc000

def z975 : W := mkw 0x33fbfb74a0000000 0x0cfefedd28000000 0xfbfffffff0000000 0x3efffffffc000000

def z976 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0xa5fc003f00ff0000 0x297f000fc03fc000

def z977 : W := mkw 0x00697932a4000000 0x001a5e4ca9000000 0xfaff3fbff0000000 0x3ebfcfeffc000000

def z978 : W := mkw 0x202403ed016903c1 0x080900fb405a40f0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z979 : W := mkw 0x08085a52cc000000 0x02021694b3000000 0xb91cfffffc000000 0x2e473fffff000000

def z980 : W := mkw 0x4b228bf8f9091330 0x12c8a2fe3e4244cc 0xdb03c3f8fc000332 0xb6c0f0fe3f0000cc

def z981 : W := mkw 0x23b4036d02ec0140 0x08ed00db40bb0050 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z982 : W := mkw 0x17dff64002f6ec00 0x85f7fd9000bdbb00 0xffffffc003fffc00 0x3ffffff000ffff00

def z983 : W := mkw 0x000c581384600444 0x00031604e1180111 0xbd1cfc7f8cc08fff 0xef473f1fe33023ff

def z984 : W := mkw 0xaf9282c45b805aa8 0x2be4a0b116e016aa 0xdf1fc3c7ffc0ffff 0xf7c7f0f1fff03fff

def z985 : W := mkw 0x14dd740002f6ec00 0x85375d0000bdbb00 0xb5fcfc0003fffc00 0x2d7f3f0000ffff00

def z986 : W := mkw 0x004124000012a000 0x001049000004a800 0x62e33c00033f7000 0x18b8cf0000cfdc00

def z987 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xffe33ff8f3fff3f3 0xbff8cffe3cfffcfc

def z988 : W := mkw 0x000c5c1b847aa554 0x00031706e11ea955 0xbd1cfc7f8fffffff 0xef473f1fe3ffffff

def z989 : W := mkw 0x5b4bfed2fd12b230 0x56d2ffb4bf44ac8c 0xdf03ffc0ff00f332 0xb7c0fff03fc03ccc

def z990 : W := mkw 0x386bfb76ec000000 0x4e1afeddbb000000 0xb91ffffffc000000 0x2e47ffffff000000

def z991 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfbfffffffc008c3c 0xfeffffffff00230f

def z992 : W := mkw 0x00497c128412a414 0x00125f04a104a905 0x1003fc008c00fc3c 0xc400ff0023003f0f

def z993 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xf3ffffbf70000000 0x3cffffefdc000000

def z994 : W := mkw 0x17dff40206f6ec04 0x85f7fd0081bdbb01 0xf7fffc000ffffc0c 0x7dffff0003ffff03

def z995 : W := mkw 0x006125a8111bb320 0x0018496a0446ecc8 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z996 : W := mkw 0x4004048913ffb7f5 0x1001012244ffedfd 0x0400000003ffffff 0xc100000000ffffff

def z997 : W := mkw 0x0004000900680140 0x00010002401a0050 0xeffc007f03ff03c3 0x3bff001fc0ffc0f0

def z998 : W := mkw 0x23b403ed13ed13e1 0x08ed00fb44fb44f8 0xffffc3ffffffffff 0xfffff0ffffffffff

def z999 : W := mkw 0x13dff40002f6a000 0x04f7fd0000bda800 0xf7fffc0003fff000 0x3dffff0000fffc00

def z1000 : W := mkw 0xa4b401ad13ed5be9 0x292d006b44fb56fa 0x24fc003f03ffffff 0xc93f000fc0ffffff

def z1001 : W := mkw 0x20b401ad116d1361 0x082d006b445b44d8 0xfeff03bff33ff332 0xbfbfc0effccffccc

def z1002 : W := mkw 0xafb683ed4bed4bc9 0x2beda0fb52fb52f2 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z1003 : W := mkw 0xbfdff6464ef6ec88 0xeff7fd9193bdbb22 0xf7fffc470ffffccd 0x7dffff11c3ffff33

def z1004 : W := mkw 0x17d3a4000296e800 0x85f4e90000a5ba00 0x62e33c00033f7000 0x18b8cf0000cfdc00

def z1005 : W := mkw 0x0796800902ec4940 0x01e5a00240bb1250 0xffffc07f8fffffff 0xfffff01fe3ffffff

def z1006 : W := mkw 0x10497c128412a414 0x84125f04a104a905 0x1000fc008c008c3c 0xc4003f002300230f

def z1007 : W := mkw 0x14dd740002f6ec00 0x85375d0000bdbb00 0xf6ff3c0003fffc00 0x3dbfcf0000ffff00

def z1008 : W := mkw 0x37dff40606f6ec00 0xcdf7fd0181bdbb00 0xf7fffc0703fffc00 0x3dffff01c0ffff00

def z1009 : W := mkw 0x3bfbfb76ee800080 0x4efefeddbba00020 0xfbfffffffcc000c1 0x3effffffff300030

def z1010 : W := mkw 0x0443a4000012e800 0x0110e9000004ba00 0xf6e3fc00033ffc00 0x3db8ff0000cfff00

def z1011 : W := mkw 0x23b4036502e400c1 0x08ed00d940b90030 0xeffc03ff03ff00c1 0x3bff00ffc0ffc030

def z1012 : W := mkw 0xabb403ed5bed13e9 0x2aed00fb56fb44fa 0xfffcc3ffffff8fff 0xffff30ffffffe3ff

def z1013 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xfffffc408ffffc00 0x3fffff1023ffff00

def z1014 : W := mkw 0x8404048913ffffe9 0xa101012244fffffa 0x0400000003ffffff 0xc100000000ffffff

def z1015 : W := mkw 0x8c02808059005a28 0x2300a0201640168a 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z1016 : W := mkw 0x2bf3ab74e8000000 0x0afceadd3a000000 0xfbfffffffc000000 0x3effffffff000000

def z1017 : W := mkw 0x2b2adb76ec000000 0x4acab6ddbb000000 0xfb1ffffffc000000 0x3ec7ffffff000000

def z1018 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xefffc3ff7fff7fcf 0x7bfff0ffdfffdff3

def z1019 : W := mkw 0x1fdff6404af6ec00 0x87f7fd9012bdbb00 0xffffffc0ffffffff 0xfffffff03fffffff

def z1020 : W := mkw 0x7bbadbfefd091330 0x5eeeb6ffbf4244cc 0x091cc3fffc000332 0x824730ffff0000cc

def z1021 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xeee33fb8733f7302 0x3bb8cfee1ccfdcc0

def z1022 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xffff03fff3fff3f3 0xbfffc0fffcfffcfc

def z1023 : W := mkw 0x000c5c1b847ea554 0x80031706e11fa955 0xbd1cfc7f8cff8fff 0xef473f1fe33fe3ff

def z1024 : W := mkw 0x40200bf8b10913b0 0x100802fe2c4244ec 0x080003f8f00003f3 0x820000fe3c0000fc

def z1025 : W := mkw 0x602009bdb1091371 0x1808026f6c4244dc 0x080003bff0000332 0x820000effc0000cc

def z1026 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xfee33fb8f3ffffff 0xffb8cfee3cffffff

def z1027 : W := mkw 0x3bb683ed4bed03c1 0x4eeda0fb52fb40f0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z1028 : W := mkw 0x38fbfb76ec000000 0x4e3efeddbb000000 0x38fffffffc000000 0x0e3fffffff000000

def z1029 : W := mkw 0x17dbf4000296e800 0x85f6fd0000a5ba00 0xf7fffc00033ff000 0x3dffff0000cffc00

def z1030 : W := mkw 0x3ffbfb76ee844800 0xcffefeddbba11200 0xfbfffffffc000000 0x3effffffff000000

def z1031 : W := mkw 0x004124000012a000 0x001049000004a800 0xfee33c00833ff332 0xbfb8cf0020cffccc

def z1032 : W := mkw 0x1c4bfc12ec12ec14 0xc712ff04bb04bb05 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z1033 : W := mkw 0x17dff40002f6ec14 0x85f7fd0000bdbb05 0xf7fffc0003fffc3c 0xfdffff0000ffff0f

def z1034 : W := mkw 0x00085c1284108414 0x00021704a1042105 0xbd1cfc7f8cc08fff 0xef473f1fe33023ff

def z1035 : W := mkw 0x27b403ed03ed4fc1 0x89ed00fb40fb53f0 0xeffc03ff03ff0fc3 0x3bff00ffc0ffc3f0

def z1036 : W := mkw 0x50497c12b412b030 0x54125f04ad04ac0c 0x10033c00f000f030 0x8400cf003c003c0c

def z1037 : W := mkw 0x33f97b76a4000000 0x4cfe5edda9000000 0xfbff3ffff0000000 0x3effcffffc000000

def z1038 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0x56e3fc0003fffc00 0x15b8ff0000ffff00

def z1039 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0xacfc003f003f0302 0x2b3f000fc00fc0c0

def z1040 : W := mkw 0x23b4012d006d0141 0x08ed004b401b4050 0xe3fc003f003f0000 0x38ff000fc00fc000

def z1041 : W := mkw 0xbffbfb76ec004808 0x6ffefeddbb001202 0xfbfffffffc000c0c 0x7effffffff000303

def z1042 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0x080003f8fc0003ff 0xc20000fe3f0000ff

def z1043 : W := mkw 0x03b401a903ed0340 0x00ed006a40fb40d0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z1044 : W := mkw 0x4004048911799774 0x10010122445e65dd 0x0400000000f88fff 0xc1000000003e23ff

def z1045 : W := mkw 0x63b40bfdb3ed13f1 0x18ed02ff6cfb44fc 0x091c03fff0c003f3 0x824700fffc3000fc

def z1046 : W := mkw 0x13dff4000076a400 0x84f7fd00001da900 0xf7fffc00033ff000 0x3dffff0000cffc00

def z1047 : W := mkw 0x3fdff6444af6ec00 0xcff7fd9112bdbb00 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z1048 : W := mkw 0x8f0282c05b805aa8 0x23c0a0b016e016aa 0xff1fc3ffffc0ffff 0xffc7f0fffff03fff

def z1049 : W := mkw 0x0b43a6404812a000 0x02d0e9901204a800 0xffe3ffc0ff3ff000 0x3ff8fff03fcffc00

def z1050 : W := mkw 0x0743a4000292e800 0x01d0e90000a4ba00 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z1051 : W := mkw 0x40612db9b11bb3f1 0x10184b6e6c46ecfc 0xfee33fb8f33ff3f3 0xbfb8cfee3ccffcfc

def z1052 : W := mkw 0x38f97b76ec000000 0x4e3e5eddbb000000 0xfaff3ffffc000000 0x3ebfcfffff000000

def z1053 : W := mkw 0x004d74030472a444 0x00135d00c11ca911 0xf7fffc470ffffccd 0x7dffff11c3ffff33

def z1054 : W := mkw 0x144bfc128412ec00 0x8512ff04a104bb00 0x1003fc008c00fc00 0x0400ff0023003f00

def z1055 : W := mkw 0xcf4bfed2ff92febc 0x33d2ffb4bfe4bfaf 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z1056 : W := mkw 0x27b403ed03ed4bc1 0x09ed00fb40fb52f0 0xeffc03ff03ffffc3 0x3bff00ffc0fffff0

def z1057 : W := mkw 0x1f4bfe52ee92ec00 0xc7d2ff94bba4bb00 0xdf03ffc0ffc0fc00 0x37c0fff03ff03f00

def z1058 : W := mkw 0x28697b76ec000000 0x4a1a5eddbb000000 0xfbfffffffc000000 0x3effffffff000000

def z1059 : W := mkw 0x2bb403ed6bed03c1 0x4aed00fb5afb40f0 0xeffc03ff73ff03c3 0x3bff00ffdcffc0f0

def z1060 : W := mkw 0x4404048913fffff1 0x9101012244fffffc 0x0400000003fffff3 0x8100000000fffffc

def z1061 : W := mkw 0x03dd740002f6a400 0x00f75d0000bda900 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z1062 : W := mkw 0x004124000012a000 0x001049000004a800 0xffe3fc408fffffff 0xfff8ff1023ffffff

def z1063 : W := mkw 0xa7b683ed13ed5be9 0x29eda0fb44fb56fa 0xffffc3ff03ffffff 0xfffff0ffc0ffffff

def z1064 : W := mkw 0xbf9282c45b805aa8 0x6fe4a0b116e016aa 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z1065 : W := mkw 0x23b4036d006d0141 0x08ed00db401b4050 0x62fc03bf003f0000 0x18bf00efc00fc000

def z1066 : W := mkw 0x004974000012a000 0x00125d000004a800 0xf7fffc00033ff000 0x3dffff0000cffc00

def z1067 : W := mkw 0xa3b403ed13ed13e9 0x28ed00fb44fb44fa 0xeffc03ff03ff03ff 0xfbff00ffc0ffc0ff

def z1068 : W := mkw 0x17dbf4000292e800 0x05f6fd0000a4ba00 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z1069 : W := mkw 0x40612db0b113b230 0x10184b6c2c44ec8c 0xf6e33f80f33ff030 0xbdb8cfe03ccffc0c

def z1070 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfffffffffcc003c3 0x3fffffffff3000f0

def z1071 : W := mkw 0x3fdff6464ef6ec00 0xcff7fd9193bdbb00 0xffffffc7fffffc00 0x3ffffff1ffffff00

def z1072 : W := mkw 0x17dff40206f6ec00 0x85f7fd0081bdbb00 0xf7fffc470ffffc00 0x3dffff11c3ffff00

def z1073 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xfee33ff8ff3ff3ff 0xffb8cffe3fcffcff

def z1074 : W := mkw 0x70fd7d3fa47ba554 0x5c3f5f4fe91ee955 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z1075 : W := mkw 0xcc4bfc12fc12fc3c 0x3312ff04bf04bf0f 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z1076 : W := mkw 0x40497c12b412b434 0x10125f04ad04ad0d 0x10033c00f000f030 0x8400cf003c003c0c

def z1077 : W := mkw 0x0747a40002f6ec00 0x81d1e90000bdbb00 0xf7e3fc0003fffc00 0x3df8ff0000ffff00

def z1078 : W := mkw 0x0045240002f6a000 0x0011490000bda800 0xf6e33c0003fff000 0x3db8cf0000fffc00

def z1079 : W := mkw 0xa7b403ed13ed5be9 0x29ed00fb44fb56fa 0xeffc03ff03ff73c3 0x3bff00ffc0ffdcf0

def z1080 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0xeafc03bf003f0000 0x3abf00efc00fc000

def z1081 : W := mkw 0x0394008903ed03c1 0x00e5002240fb40f0 0xeffc007f03ff03c3 0x3bff001fc0ffc0f0

def z1082 : W := mkw 0x17dff40306f6ec44 0x85f7fd00c1bdbb11 0xfffffc478fffffff 0xffffff11e3ffffff

def z1083 : W := mkw 0x00612db8a11ba300 0x00184b6e2846e8c0 0xfee33fb8f33ff302 0x3fb8cfee3ccffcc0

def z1084 : W := mkw 0x63b403ed33ed13e1 0x18ed00fb4cfb44f8 0xeffc03ff73ff03c3 0x3bff00ffdcffc0f0

def z1085 : W := mkw 0x002001a801090300 0x0008006a004240c0 0xeffc03ff033f0302 0x3bff00ffc0cfc0c0

def z1086 : W := mkw 0x3bfbf36468000000 0x4efefcd91a000000 0xfbffffff70000000 0x3effffffdc000000

def z1087 : W := mkw 0xaf9ed2474ee44ccd 0x2be7b491d3b91333 0x011cc0470cc00ccd 0x40473011c3300333

def z1088 : W := mkw 0x68200bfffd091374 0x5a0802ffff4244dd 0x080003fffc0003ff 0xc20000ffff0000ff

def z1089 : W := mkw 0x186bf932ec000000 0x461afe4cbb000000 0xfbfffffffc000000 0x3effffffff000000

def z1090 : W := mkw 0x9f9ed2404ae44c88 0xa7e7b49012b91322 0x011cc00000c00c00 0x0047300000300300

def z1091 : W := mkw 0x40612db0b113b220 0x10184b6c2c44ec88 0xfee33fb8f33ff000 0x3fb8cfee3ccffc00

def z1092 : W := mkw 0x60200bfcb10913b1 0x180802ff2c4244ec 0x080003b8f0000332 0x820000ee3c0000cc

def z1093 : W := mkw 0x482009bafd091330 0x5208026ebf4244cc 0x080003b8fc000332 0x820000ee3f0000cc

def z1094 : W := mkw 0x23b403ed016d0341 0x08ed00fb405b40d0 0xeffc03ff033f0302 0x3bff00ffc0cfc0c0

def z1095 : W := mkw 0x0b6bfb72ec000000 0x02dafedcbb000000 0xfbfffffffc000000 0x3effffffff000000

def z1096 : W := mkw 0x03d124000012a000 0x00f449000004a800 0xf7ff3c00033ff000 0x3dffcf0000cffc00

def z1097 : W := mkw 0x20b4012d006d0141 0x082d004b401b4050 0xa9fc007f003f0000 0x2a7f001fc00fc000

def z1098 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xf3fffc00033f7000 0x3cffff0000cfdc00

def z1099 : W := mkw 0xbbfbfb76ec000088 0x6efefeddbb000022 0xfbfffffffc0000cd 0x7effffffff000033

def z1100 : W := mkw 0x00040c1980788150 0x00010306601e2054 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z1101 : W := mkw 0x20f12934a0000000 0x083c4a4d28000000 0xfaff3fbff0000000 0x3ebfcfeffc000000

def z1102 : W := mkw 0x1bdbfa52cc000000 0x06f6fe94b3000000 0xfbfffffffc000000 0x3effffffff000000

def z1103 : W := mkw 0xc404048913fbfffc 0x3101012244feffff 0x0400000003ffffff 0xc100000000ffffff

def z1104 : W := mkw 0x000c581b84680140 0x00031606e11a0050 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z1105 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0x25fcfc0003fffc00 0x097f3f0000ffff00

def z1106 : W := mkw 0x9fdff6404af6ec88 0xa7f7fd9012bdbb22 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z1107 : W := mkw 0x3ffbfb76ec026800 0xcffefeddbb009a00 0xfbfffffffc007000 0x3effffffff001c00

def z1108 : W := mkw 0x044124000296e800 0x8110490000a5ba00 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z1109 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfaff3fbff0000000 0x3ebfcfeffc000000

def z1110 : W := mkw 0x23b4012d02ed0141 0x08ed004b40bb4050 0x62fc003f033f0000 0x18bf000fc0cfc000

def z1111 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xfffcc3ff8fff03c3 0x3fff30ffe3ffc0f0

def z1112 : W := mkw 0x97dff40002f6ec88 0xa5f7fd0000bdbb22 0xf7fffc0003fffccd 0x7dffff0000ffff33

def z1113 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xffffc3ffffff73c3 0x3ffff0ffffffdcf0

def z1114 : W := mkw 0x23b4036d02ed0141 0x08ed00db40bb4050 0xeffc03ff03ff0000 0x3bff00ffc0ffc000

def z1115 : W := mkw 0x68200bfcf9091330 0x5a0802ff3e4244cc 0x080003b8f0000332 0x820000ee3c0000cc

def z1116 : W := mkw 0x2bb85b76ec000000 0x4aee16ddbb000000 0xfbfcfffffc000000 0x3eff3fffff000000

def z1117 : W := mkw 0x23b4012402e40000 0x08ed004900b90000 0xe7fc003f03ff0000 0x39ff000fc0ffc000

def z1118 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0x66ff3c0003fffc00 0x19bfcf0000ffff00

def z1119 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0xda0303b8f0000332 0xb680c0ee3c0000cc

def z1120 : W := mkw 0x8c0282c059005aa8 0x2300a0b0164016aa 0x9d03c3c0fcc0ffff 0xe740f0f03f303fff

def z1121 : W := mkw 0x23b401ad03ed03c1 0x08ed006b40fb40f0 0xe7fc003f03ff03c3 0x39ff000fc0ffc0f0

def z1122 : W := mkw 0x1fdff6404af6ec00 0x87f7fd9012bdbb00 0xf7fffc400ffffc00 0x3dffff1003ffff00

def z1123 : W := mkw 0x20b4036d006d0141 0x082d00db401b4050 0x28fc03ff003f0000 0x0a3f00ffc00fc000

def z1124 : W := mkw 0x3bfbfb76ec000014 0x4efefeddbb000005 0xfbfffffffc00003c 0xfeffffffff00000f

def z1125 : W := mkw 0x3ffbfb76ec004c00 0xcffefeddbb001300 0xfbfffffffc000c00 0x3effffffff000300

def z1126 : W := mkw 0x20b4012400640000 0x082d004900190000 0x20fc003f003f0000 0x083f000fc00fc000

def z1127 : W := mkw 0x40412488111bb330 0x101049220446eccc 0xfee33f80f33ff332 0xbfb8cfe03ccffccc

def z1128 : W := mkw 0x004524000076a400 0x80114900001da900 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z1129 : W := mkw 0x40612dbab51bb334 0x10184b6ead46eccd 0xfee33fb8ff3ff33e 0xffb8cfee3fcffccf

def z1130 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xfffcc3ff03ff8fc3 0x3fff30ffc0ffe3f0

def z1131 : W := mkw 0x07d7a40002f6e800 0x01f5e90000bdba00 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z1132 : W := mkw 0x8404048913fefffc 0xa101012244ffbfff 0x0400000003ffffff 0xc100000000ffffff

def z1133 : W := mkw 0x3bfbfb76ec062000 0xcefefeddbb018800 0xfbfffffffc070000 0x3effffffff01c000

def z1134 : W := mkw 0x20b401ad016d03c1 0x082d006b405b40f0 0x20fc003f003f03c3 0x083f000fc00fc0f0

def z1135 : W := mkw 0x184bfc12ec12a400 0xc612ff04bb04a900 0x1003fc00fc000000 0x0400ff003f000000

def z1136 : W := mkw 0x60200bffb50913f5 0x180802ffed4244fd 0x080003fffc0003ff 0xc20000ffff0000ff

def z1137 : W := mkw 0x1443a4000012e800 0x8510e9000004ba00 0xf6e33c00033ff000 0x3db8cf0000cffc00

def z1138 : W := mkw 0x2fb683644ae44800 0x0beda0d912b91200 0xffffc3fffffffc00 0x3ffff0ffffffff00

def z1139 : W := mkw 0x10dd74000076a400 0x84375d00001da900 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z1140 : W := mkw 0x2fb683ed4bed4bc1 0x0beda0fb52fb52f0 0xffffc3ffffffffc3 0x3ffff0fffffffff0

def z1141 : W := mkw 0x402009b9b10913f1 0x1008026e6c4244fc 0x080003b8f00003f3 0x820000ee3c0000fc

def z1142 : W := mkw 0xbffbfb76ee804888 0x6ffefeddbba01222 0xfffffffffcc08fff 0xffffffffff3023ff

def z1143 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0x66fc03bf03ff03c3 0x19bf00efc0ffc0f0

def z1144 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0x63ffffff7c000000 0x18ffffffdf000000

def z1145 : W := mkw 0x3f9ed2474ee44cc1 0xcfe7b491d3b91330 0x011cc0470cc00cc1 0x00473011c3300330

def z1146 : W := mkw 0x044124000292e800 0x0110490000a4ba00 0xf6e33c0003fffc00 0x3db8cf0000ffff00

def z1147 : W := mkw 0x402009b9b1091370 0x1008026e6c4244dc 0x080003fff00003f3 0x820000fffc0000fc

def z1148 : W := mkw 0x00412c98911ab330 0x00104b262446accc 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z1149 : W := mkw 0x3fdff6474ef6ec44 0xcff7fd91d3bdbb11 0xf7fffc470ffffccd 0x7dffff11c3ffff33

def z1150 : W := mkw 0x23b403ed13ed13e1 0x08ed00fb44fb44f8 0xefff03ff73ff73c3 0x3bffc0ffdcffdcf0

def z1151 : W := mkw 0x23b4036d006d0141 0x08ed00db401b4050 0x21fc007f003f0000 0x087f001fc00fc000

def z1152 : W := mkw 0x0394000902ec0140 0x00e5000240bb0050 0xe7fc003f03ff0000 0x39ff000fc0ffc000

def z1153 : W := mkw 0x30fd7d3fa47ea554 0xcc3f5f4fe91fa955 0x20fc3c3f003f0000 0x083f0f0fc00fc000

def z1154 : W := mkw 0x400c5c1b847ba554 0x10031706e11ee955 0xbd1cfc7f8cff8fff 0xef473f1fe33fe3ff

def z1155 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0x56e33f80f33ff332 0x95b8cfe03ccffccc

def z1156 : W := mkw 0x13dff4000072a400 0x04f7fd00001ca900 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z1157 : W := mkw 0x20b401ad03ed03c1 0x082d006b40fb40f0 0xeefc03bf03ff03c3 0x3bbf00efc0ffc0f0

def z1158 : W := mkw 0x8408589297805aa8 0x21021624a5e016aa 0xbd1cfc7f8fc0ffff 0xef473f1fe3f03fff

def z1159 : W := mkw 0x38f97b76ec000000 0x4e3e5eddbb000000 0xb9fcfffffc000000 0x2e7f3fffff000000

def z1160 : W := mkw 0x20b001ac01090300 0x082c006b004240c0 0xeefc03bf033f0302 0x3bbf00efc0cfc0c0

def z1161 : W := mkw 0x8400008013805aa8 0x2100002004e016aa 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z1162 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0x25fc007f03ff03c3 0x097f001fc0ffc0f0

def z1163 : W := mkw 0xbf9ed2454ae44cc9 0xafe7b49152b91332 0x011cc0470cc00ccd 0x40473011c3300333

def z1164 : W := mkw 0xa8b403ed596d13e9 0x2a2d00fb565b44fa 0x28fc03fffc3f03ff 0xca3f00ffff0fc0ff

def z1165 : W := mkw 0x079ed40002f4cc00 0x01e7b50000bd3300 0xf7fffc0003fffc00 0x3dffff0000ffff00

def z1166 : W := mkw 0x48200bf8f9091330 0x120802fe3e4244cc 0x080003f8fc000332 0x820000fe3f0000cc

def z1167 : W := mkw 0x17dff40102f6ec44 0x85f7fd0040bdbb11 0xf7fffc0003fffccd 0x7dffff0000ffff33

def z1168 : W := mkw 0xabb683ed5bed13e9 0x2aeda0fb56fb44fa 0xffffc3ffffff03ff 0xfffff0ffffffc0ff

def z1169 : W := mkw 0x144ff40002f6ec00 0x8513fd0000bdbb00 0xf6e3fc0003fffc00 0x3db8ff0000ffff00

def z1170 : W := mkw 0x37b683ed03ed4bc1 0x8deda0fb40fb52f0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z1171 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xffff3ffff33ff332 0xbfffcffffccffccc

def z1172 : W := mkw 0x20b401ad03ed03c1 0x082d006b40fb40f0 0xadfc007f03ff03c3 0x2b7f001fc0ffc0f0

def z1173 : W := mkw 0x406125a03113b220 0x101849680c44ec88 0x62e33f80733f7000 0x18b8cfe01ccfdc00

def z1174 : W := mkw 0x5c4bfc12fc12fc30 0xd712ff04bf04bf0c 0x1003fc00fc00fc30 0x8400ff003f003f0c

def z1175 : W := mkw 0x0008581b84080154 0x00021606e1020055 0xbd1cfc7f8cc08fff 0xef473f1fe33023ff

def z1176 : W := mkw 0x000c5c1b84788554 0x00031706e11e2155 0xff1ffffffcf88fff 0xffc7ffffff3e23ff

def z1177 : W := mkw 0x8c0282c05b805aa8 0x2300a0b016e016aa 0x1c03c3c0ffc0ffff 0xc700f0f03ff03fff

def z1178 : W := mkw 0x0445240002f6ec00 0x8111490000bdbb00 0x24e03c0003fffc00 0x09380f0000ffff00

def z1179 : W := mkw 0x8f02824058005828 0x23c0a0901600160a 0xdf03c3c0fcc0ffff 0xf7c0f0f03f303fff

def z1180 : W := mkw 0x002401a903ed03c1 0x0009006a40fb40f0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z1181 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0x6ae33fb8f33f7332 0x9ab8cfee3ccfdccc

def z1182 : W := mkw 0x17dbf4000012ec00 0x85f6fd000004bb00 0xf7fffc00033ffc00 0x3dffff0000cfff00

def z1183 : W := mkw 0x10d974000012a000 0x04365d000004a800 0xf6ff3c00033ff000 0x3dbfcf0000cffc00

def z1184 : W := mkw 0x4404048913ffff74 0x9101012244ffffdd 0x0400000003ffffff 0xc100000000ffffff

def z1185 : W := mkw 0x40497c12b412b030 0x10125f04ad04ac0c 0x1003fc00fc00f030 0x8400ff003f003c0c

def z1186 : W := mkw 0xafb403ed5bed5be9 0x2bed00fb56fb56fa 0xeffc03ffffffffff 0xfbff00ffffffffff

def z1187 : W := mkw 0x37dff64402f6ec00 0x8df7fd9100bdbb00 0xf7fffc4703fffc00 0x3dffff11c0ffff00

def z1188 : W := mkw 0x10497c128412a414 0x84125f04a104a905 0x00003c0000000000 0x00000f0000000000

def z1189 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0x0000003800000332 0x8000000e000000cc

def z1190 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xffff03fff3ff03c3 0x3fffc0fffcffc0f0

def z1191 : W := mkw 0x8f9282c05b805aa8 0x23e4a0b016e016aa 0xffffc3c0ffc0ffff 0xfffff0f03ff03fff

def z1192 : W := mkw 0x23b003ed010903c1 0x08ec00fb404240f0 0xeffc03ff033f03c3 0x3bff00ffc0cfc0f0

def z1193 : W := mkw 0x17d7a40002f6ec00 0x85f5e90000bdbb00 0xf6e33c0003fffc00 0x3db8cf0000ffff00

def z1194 : W := mkw 0x584bfc12ec12a010 0x5612ff04bb04a804 0x1003fc00fc000000 0x0400ff003f000000

def z1195 : W := mkw 0x7bfbfb76ec032000 0x5efefeddbb00c800 0xfbfffffffc070000 0x3effffffff01c000

def z1196 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0x62ff03bf733f7000 0x18bfc0efdccfdc00

def z1197 : W := mkw 0x2bf12b76ec000000 0x4afc4addbb000000 0xfbff3ffffc000000 0x3effcfffff000000

def z1198 : W := mkw 0x044124000012ec00 0x811049000004bb00 0xf6e33c00033ffc00 0x3db8cf0000cfff00

def z1199 : W := mkw 0x402009b8b1091330 0x1008026e2c4244cc 0x9c0003b8f0008332 0xa70000ee3c0020cc

def z1200 : W := mkw 0x80040489117897fc 0x20010122445e25ff 0x0400000000f88fff 0xc1000000003e23ff

def z1201 : W := mkw 0x23f97b76a4000000 0x08fe5edda9000000 0xfbfffffffc000000 0x3effffffff000000

def z1202 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0x63fc03ff03ff00c1 0x18ff00ffc0ffc030

def z1203 : W := mkw 0x20b403ed03ed03c1 0x082d00fb40fb40f0 0x2cfc03ff03ff03c3 0x0b3f00ffc0ffc0f0

def z1204 : W := mkw 0x27b683ed03ed4bc1 0x09eda0fb40fb52f0 0xffffc3ff8fffffff 0xfffff0ffe3ffffff

def z1205 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xffffff80f3fffc00 0x3fffffe03cffff00

def z1206 : W := mkw 0x60612dbeb51bb330 0x58184b6fad46eccc 0xfee33fbff33ff332 0xbfb8cfeffccffccc

def z1207 : W := mkw 0x20b403ed016d03c1 0x082d00fb405b40f0 0xadfc03ff00ff03c3 0x2b7f00ffc03fc0f0

def z1208 : W := mkw 0x23d5264502f6a0c1 0x08f5499140bda830 0xf7ff3c4703fff0c1 0x3dffcf11c0fffc30

def z1209 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xffe3ffb8f3ffff32 0xbff8ffee3cffffcc

def z1210 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfbfffffffc0003ff 0xfeffffffff0000ff

def z1211 : W := mkw 0xafb683ed5bed5be9 0x2beda0fb56fb56fa 0xffffc3ff73ffffc3 0x3ffff0ffdcfffff0

def z1212 : W := mkw 0xbff3a3e47b867aa8 0xeffce8f91ee19eaa 0x42e3038073077000 0x10b8c0e01cc1dc00

def z1213 : W := mkw 0x402009bab5091330 0x1008026ead4244cc 0x080003fffc000332 0x820000ffff0000cc

def z1214 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0xfae33fb8f33f7000 0x3eb8cfee3ccfdc00

def z1215 : W := mkw 0xabb403ed5bed13e9 0x2aed00fb56fb44fa 0xeffc03ff73ff03c3 0x3bff00ffdcffc0f0

def z1216 : W := mkw 0x17dd740002f6ec00 0x85f75d0000bdbb00 0xe7fc3c0003fffc00 0x39ff0f0000ffff00

def z1217 : W := mkw 0x40612d38a01ba110 0x10184b4e2806e844 0xfee33fb8f33ff000 0x3fb8cfee3ccffc00

def z1218 : W := mkw 0xdf4bfed2ff92fab8 0x77d2ffb4bfe4beae 0xdf03ffc0ffc0ffff 0xf7c0fff03ff03fff

def z1219 : W := mkw 0x20b4012d02ed01c1 0x082d004b40bb4070 0x20fc003f00ff00c1 0x083f000fc03fc030

def z1220 : W := mkw 0x10dd74000076a400 0x84375d00001da900 0x24fc3c00033ff000 0x093f0f0000cffc00

def z1221 : W := mkw 0x30f97936a4000000 0x4c3e5e4da9000000 0x28fc3fbff0000000 0x0a3f0feffc000000

def z1222 : W := mkw 0x30f97936a4000000 0x4c3e5e4da9000000 0xfbfffffffc000000 0x3effffffff000000

def z1223 : W := mkw 0x27b683ed03ed4bc1 0x09eda0fb40fb52f0 0xeffcc3ff03ff0fc3 0x3bff30ffc0ffc3f0

def z1224 : W := mkw 0x20b0012c00090100 0x082c004b00024040 0x20fc003f003f0000 0x083f000fc00fc000

def z1225 : W := mkw 0x406125a03113b220 0x101849680c44ec88 0xfee33f80f33ff332 0xbfb8cfe03ccffccc

def z1226 : W := mkw 0x17dff40002f6ec00 0x85f7fd0000bdbb00 0xf7fffc0003ffffff 0xfdffff0000ffffff

def z1227 : W := mkw 0x000c5c1284708400 0x00031704a11c2100 0xbd1cfc7f8cf88fff 0xef473f1fe33e23ff

def z1228 : W := mkw 0xc8200bfbfd0913fc 0x320802feff4244ff 0x080003fffc0003ff 0xc20000ffff0000ff

def z1229 : W := mkw 0x3b9ada56cc000000 0x4ee6b695b3000000 0xfb1ffffffc000000 0x3ec7ffffff000000

def z1230 : W := mkw 0x3f9ed2444ae44c00 0xcfe7b49112b91300 0x011cc00000c00c00 0x0047300000300300

def z1231 : W := mkw 0xabb403ed4bed03c9 0x2aed00fb52fb40f2 0xeffc03ff0fff03cf 0x7bff00ffc3ffc0f3

def z1232 : W := mkw 0x004524000072a400 0x00114900001ca900 0xf6e33c0003fffc00 0x3db8cf0000ffff00

def z1233 : W := mkw 0xc82009b8f9091338 0x3208026e3e4244ce 0x080003b8fc00033e 0xc20000ee3f0000cf

def z1234 : W := mkw 0x2bb6836d486d0141 0x0aeda0db521b4050 0xfbffc3fffc3f0000 0x3efff0ffff0fc000

def z1235 : W := mkw 0x1fdff6404af6ec00 0x87f7fd9012bdbb00 0xf7ffff8073fffc00 0x3dffffe01cffff00

def z1236 : W := mkw 0xdc4bfc12fc12f838 0x7712ff04bf04be0e 0x1003fc00fc00fc3c 0xc400ff003f003f0f

def z1237 : W := mkw 0xe8200bfefd0913b8 0x7a0802ffbf4244ee 0x080003fffc0003ff 0xc20000ffff0000ff

def z1238 : W := mkw 0x40612dbbb51bb374 0x10184b6eed46ecdd 0xffe3ffffffffffff 0xfff8ffffffffffff

def z1239 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xeffc03ff8fff03ff 0xfbff00ffe3ffc0ff

def z1240 : W := mkw 0x23b403ed01690340 0x08ed00fb405a40d0 0xeffc03ff03ff03c3 0x3bff00ffc0ffc0f0

def z1241 : W := mkw 0x40612db9b11bb374 0x10184b6e6c46ecdd 0xfee33fb8f33ff3ff 0xffb8cfee3ccffcff

def z1242 : W := mkw 0xabb403ed5bed13e9 0x2aed00fb56fb44fa 0xffff03fffffff3ff 0xffffc0fffffffcff

def z1243 : W := mkw 0x0024012900690140 0x0009004a401a4050 0x20fc003f003f0000 0x083f000fc00fc000

def z1244 : W := mkw 0x13dd740002f6a400 0x84f75d0000bda900 0xf7ff3c0003fff000 0x3dffcf0000fffc00

def z1245 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0x6aff3ffffc000000 0x1abfcfffff000000

def z1246 : W := mkw 0x00612d38a01aa110 0x00184b4e2806a844 0xfee33fb8f33ff332 0xbfb8cfee3ccffccc

def z1247 : W := mkw 0x2bb403ed4bed03c1 0x0aed00fb52fb40f0 0xeffc03ffffff03c3 0x3bff00ffffffc0f0

def z1248 : W := mkw 0x0343a4000012a000 0x00d0e9000004a800 0xf7e3fc00033ff000 0x3df8ff0000cffc00

def z1249 : W := mkw 0x40612db8b11bb330 0x10184b6e2c46eccc 0x66e33fb8733ff332 0x99b8cfee1ccffccc

def z1250 : W := mkw 0x9f9282c05b845aa8 0xa7e4a0b016e116aa 0xdf03c3c0ffc0ffff 0xf7c0f0f03ff03fff

def z1251 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfffffffffc008332 0xbfffffffff0020cc

def z1252 : W := mkw 0x3bfbfb76ec000000 0x4efefeddbb000000 0xfbfffffffcc00ccd 0x7effffffff300333

def z1253 : W := mkw 0x144bfc128412ec14 0x8512ff04a104bb05 0x1003fc000000fc00 0x0400ff0000003f00

def z1254 : W := mkw 0x8f9682c95bec5be8 0x23e5a0b256fb16fa 0xffffc3ffffffffff 0xfffff0ffffffffff

def z1255 : W := mkw 0x23b403ed03ed03c1 0x08ed00fb40fb40f0 0xeffc03ff03ff8fff 0xfbff00ffc0ffe3ff

def z1256 : W := mkw 0x37dff64706f6ecc5 0x8df7fd91c1bdbb31 0xf7fffc470ffffccd 0x7dffff11c3ffff33

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z4,z9,z5,z6]),(0,[z0,z1,z10,z3,z4,z5,z6]),(0,[z0,z11,z3,z4,z5,z6,z12]),(0,[z0,z1,z4,z5,z13,z6,z14]),(0,[z0,z1,z15,z16,z4,z5,z6]),(1,[z0,z1,z3,z17,z18,z6])],[(0,[z0,z19,z3,z4,z5,z20,z6]),(0,[z0,z1,z3,z21,z4,z5,z6]),(0,[z0,z1,z4,z22,z5,z23,z6]),(0,[z0,z1,z3,z24,z4,z5,z6])],[(0,[z0,z1,z25,z4,z5,z6,z14]),(0,[z0,z1,z3,z26,z5,z6,z27]),(0,[z0,z19,z28,z3,z4,z5,z6])],[(0,[z29,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z30,z6]),(0,[z31,z0,z1,z4,z5,z6,z14]),(0,[z1,z3,z26,z4,z5,z32,z6]),(0,[z0,z3,z4,z33,z5,z20,z6]),(0,[z0,z1,z3,z34,z4,z5,z6]),(0,[z0,z35,z3,z4,z33,z5,z6]),(0,[z0,z36,z3,z4,z33,z5,z6]),(0,[z37,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z38]),(0,[z0,z1,z3,z39,z4,z5,z6]),(0,[z0,z40,z1,z3,z4,z5,z6])],[(0,[z0,z1,z41,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z42,z6]),(0,[z0,z43,z28,z3,z4,z5,z6]),(0,[z0,z44,z1,z3,z4,z5,z6]),(0,[z0,z19,z1,z3,z4,z45,z6]),(0,[z0,z1,z3,z17,z4,z46,z6]),(0,[z0,z1,z3,z4,z5,z47,z6]),(0,[z0,z1,z3,z4,z5,z48,z6])],[(0,[z0,z49,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z50,z5,z6]),(0,[z0,z1,z3,z4,z51,z5,z6])],[(0,[z52,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z53,z6]),(0,[z54,z0,z1,z16,z4,z5,z6])],[(0,[z55,z0,z49,z3,z4,z5,z6]),(1,[z0,z56,z1,z4,z5,z6]),(0,[z0,z57,z1,z3,z4,z5,z6]),(0,[z58,z0,z1,z3,z59,z5,z6]),(0,[z0,z1,z60,z3,z4,z5,z6]),(0,[z0,z61,z1,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z13,z6]),(0,[z0,z1,z3,z4,z5,z6,z62]),(0,[z0,z1,z3,z4,z63,z5,z6]),(0,[z0,z1,z3,z4,z5,z64,z6]),(0,[z65,z0,z1,z3,z4,z5,z6]),(1,[z0,z66,z1,z3,z5,z27])]],
   [[(0,[z0,z1,z67,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z20,z6]),(0,[z68,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z69,z4,z5,z6,z14]),(0,[z0,z3,z4,z33,z5,z70,z6]),(0,[z0,z66,z1,z16,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z71,z6]),(0,[z0,z1,z72,z3,z4,z5,z6]),(1,[z0,z43,z73,z4,z5,z6]),(0,[z74,z0,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z75,z4,z5,z6]),(0,[z0,z1,z3,z76,z5,z70,z6])],[(0,[z0,z1,z77,z4,z5,z70,z6])],[(1,[z78,z0,z1,z79,z5,z6]),(0,[z0,z1,z16,z4,z5,z6,z14]),(1,[z0,z3,z4,z5,z6,z80])],[(0,[z0,z81,z1,z3,z4,z5,z6]),(0,[z82,z0,z19,z3,z4,z5,z6])],[(0,[z0,z1,z83,z3,z4,z5,z6]),(0,[z84,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z85]),(0,[z0,z11,z1,z86,z4,z5,z6]),(1,[z0,z87,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z70,z6])],[(0,[z0,z1,z3,z4,z5,z88,z6]),(0,[z0,z89,z1,z3,z4,z5,z6]),(0,[z0,z1,z26,z4,z5,z6,z14]),(0,[z0,z28,z3,z4,z33,z5,z6]),(0,[z82,z0,z1,z3,z4,z5,z6]),(0,[z0,z90,z1,z3,z4,z5,z6]),(0,[z91,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z92,z3,z4,z5,z6]),(0,[z93,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z94,z3,z4,z5,z6]),(0,[z95,z96,z1,z3,z4,z5,z6]),(0,[z58,z0,z1,z3,z97,z5,z6]),(1,[z0,z1,z3,z4,z98,z6])]],
   [[(0,[z58,z0,z1,z3,z4,z5,z99]),(1,[z0,z3,z4,z33,z5,z6]),(0,[z0,z100,z3,z4,z33,z5,z6]),(0,[z0,z100,z1,z3,z17,z4,z6]),(0,[z0,z1,z16,z4,z5,z101,z6])],[(0,[z0,z1,z102,z3,z4,z5,z6]),(0,[z0,z103,z1,z3,z4,z5,z6]),(0,[z0,z104,z1,z79,z4,z5,z6]),(1,[z0,z1,z3,z4,z105,z70])],[(0,[z0,z1,z3,z106,z4,z5,z6]),(0,[z58,z0,z19,z3,z4,z5,z6]),(0,[z0,z1,z107,z3,z4,z5,z6]),(0,[z0,z11,z1,z3,z108,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z109]),(0,[z0,z1,z3,z4,z5,z6,z110]),(0,[z0,z66,z111,z3,z4,z5,z6])],[(0,[z0,z1,z3,z112,z4,z5,z6]),(0,[z0,z113,z1,z3,z4,z5,z6]),(0,[z0,z1,z114,z3,z4,z5,z6])],[(0,[z115,z0,z1,z3,z4,z5,z6]),(0,[z58,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z116,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z117,z5,z6])],[(0,[z29,z55,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z118,z4,z5,z6]),(0,[z95,z0,z3,z4,z33,z5,z6]),(0,[z0,z19,z3,z4,z5,z5,z6]),(1,[z0,z19,z3,z4,z33,z6]),(0,[z0,z119,z1,z3,z4,z5,z6]),(1,[z0,z120,z3,z4,z5,z121]),(0,[z0,z1,z4,z5,z6,z14,z122]),(0,[z0,z36,z1,z16,z4,z5,z6]),(0,[z0,z1,z4,z5,z70,z6,z123])],[(0,[z0,z1,z3,z4,z124,z5,z6]),(0,[z0,z1,z3,z4,z5,z125,z6]),(0,[z0,z1,z3,z126,z4,z5,z6]),(0,[z0,z1,z3,z127,z5,z6,z27]),(0,[z0,z1,z128,z4,z117,z5,z6]),(0,[z0,z1,z16,z129,z4,z5,z6])],[(0,[z0,z3,z4,z33,z5,z5,z6]),(0,[z0,z1,z16,z3,z4,z5,z14])]],
   [[(0,[z0,z25,z3,z4,z33,z5,z6]),(0,[z52,z0,z1,z16,z4,z5,z6]),(0,[z0,z1,z130,z3,z4,z5,z6]),(0,[z7,z0,z66,z1,z3,z5,z6]),(0,[z1,z3,z4,z131,z5,z20,z6]),(0,[z0,z132,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z133,z46,z6])],[(0,[z0,z134,z1,z3,z4,z127,z6]),(0,[z0,z1,z135,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z121,z6,z14]),(0,[z0,z1,z3,z4,z5,z6,z136])],[(0,[z0,z19,z137,z3,z4,z5,z6]),(1,[z0,z4,z33,z5,z6,z14]),(1,[z0,z1,z92,z4,z5,z6]),(0,[z0,z1,z138,z3,z4,z5,z6]),(0,[z0,z1,z4,z18,z5,z6,z14]),(0,[z0,z1,z16,z4,z18,z5,z6])],[(0,[z0,z139,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z20,z6,z140]),(0,[z0,z1,z3,z5,z141,z6,z99]),(0,[z142,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z17,z18,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z143]),(0,[z0,z1,z3,z4,z5,z6,z144])],[(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z5,z145,z6]),(0,[z0,z1,z3,z146,z4,z5,z6])],[(0,[z31,z0,z28,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z121,z6,z147]),(0,[z0,z1,z148,z3,z4,z5,z6])],[(0,[z0,z49,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z8,z5,z6,z27]),(1,[z0,z149,z3,z4,z5,z6]),(0,[z0,z150,z19,z3,z4,z5,z6]),(0,[z0,z19,z79,z3,z4,z5,z6]),(0,[z0,z1,z4,z33,z5,z6,z14]),(0,[z151,z0,z1,z16,z4,z5,z6])],[(0,[z84,z0,z1,z16,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z6,z152]),(0,[z153,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z154]),(0,[z0,z155,z1,z4,z5,z6,z14]),(0,[z0,z1,z16,z4,z5,z46,z6]),(0,[z0,z1,z3,z4,z5,z6,z156])]],
   [[(0,[z157,z0,z1,z3,z4,z5,z6]),(0,[z0,z158,z1,z4,z5,z20,z6]),(0,[z0,z19,z3,z4,z131,z5,z6]),(0,[z0,z19,z3,z73,z4,z5,z6]),(0,[z0,z150,z1,z3,z4,z5,z6]),(0,[z0,z28,z1,z16,z4,z5,z6]),(0,[z159,z0,z19,z3,z4,z5,z6]),(0,[z0,z160,z1,z3,z4,z5,z6]),(0,[z0,z1,z161,z3,z4,z23,z6])],[(0,[z0,z1,z137,z3,z4,z5,z6]),(0,[z0,z19,z3,z26,z4,z5,z6]),(0,[z58,z0,z1,z3,z4,z162,z6]),(0,[z0,z163,z1,z3,z4,z5,z6])],[(0,[z164,z0,z1,z3,z4,z5,z6]),(0,[z165,z0,z1,z3,z4,z5,z6]),(0,[z0,z166,z1,z3,z4,z5,z6]),(0,[z0,z43,z3,z73,z4,z5,z6]),(1,[z0,z167,z3,z127,z5,z6]),(0,[z159,z0,z1,z3,z4,z5,z6]),(0,[z0,z100,z1,z16,z4,z5,z6]),(1,[z0,z1,z16,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z168,z6]),(0,[z0,z1,z169,z3,z4,z5,z6]),(0,[z0,z1,z170,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z171]),(0,[z0,z1,z3,z4,z5,z172,z6]),(0,[z0,z3,z173,z4,z33,z5,z6]),(0,[z174,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z175,z140])],[(0,[z0,z1,z3,z4,z5,z176,z6]),(0,[z0,z177,z1,z3,z4,z5,z6]),(0,[z0,z1,z178,z3,z4,z5,z6]),(0,[z0,z43,z1,z79,z4,z5,z6]),(0,[z78,z0,z19,z3,z4,z5,z6]),(0,[z0,z1,z179,z3,z4,z5,z6]),(1,[z0,z1,z3,z5,z6,z180])],[(1,[z0,z181,z3,z4,z5,z6]),(0,[z58,z0,z1,z3,z4,z5,z32]),(0,[z0,z1,z3,z4,z5,z182,z6])],[(0,[z58,z0,z1,z3,z4,z105,z5]),(0,[z183,z0,z1,z4,z5,z6,z14]),(0,[z0,z184,z19,z3,z4,z5,z6]),(0,[z0,z1,z3,z185,z4,z5,z6]),(0,[z0,z1,z4,z5,z70,z6,z14]),(0,[z0,z186,z1,z16,z4,z5,z6])],[(0,[z0,z187,z1,z3,z4,z5,z6]),(0,[z0,z188,z1,z3,z4,z5,z6]),(0,[z0,z189,z1,z3,z4,z5,z6]),(0,[z190,z0,z1,z3,z4,z5,z6]),(1,[z0,z191,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z192]),(0,[z0,z1,z3,z4,z5,z193,z6]),(0,[z0,z184,z1,z3,z4,z5,z6]),(0,[z0,z194,z3,z4,z33,z5,z6]),(0,[z78,z0,z1,z128,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z195,z6]),(0,[z0,z1,z3,z196,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z197]),(0,[z0,z1,z198,z3,z4,z5,z6]),(0,[z0,z1,z199,z4,z5,z46,z6])],[(0,[z200,z0,z1,z3,z4,z5,z6]),(0,[z29,z0,z137,z3,z4,z5,z6]),(0,[z0,z137,z3,z4,z5,z6,z12]),(0,[z201,z0,z1,z3,z4,z5,z6]),(0,[z0,z202,z1,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z121,z6]),(0,[z0,z1,z3,z4,z203,z5,z6]),(0,[z0,z1,z3,z4,z204,z5,z6]),(0,[z0,z1,z77,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z14,z136]),(1,[z0,z1,z146,z4,z5,z6])],[(0,[z31,z84,z1,z3,z4,z5,z6]),(0,[z0,z1,z205,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z121,z6]),(0,[z0,z120,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z206,z5,z6]),(0,[z0,z1,z3,z4,z5,z207,z6]),(0,[z0,z155,z1,z3,z4,z5,z14]),(0,[z0,z1,z3,z4,z208,z5,z6]),(1,[z0,z1,z209,z4,z5,z6])],[(0,[z31,z0,z1,z25,z4,z5,z6]),(1,[z0,z111,z3,z4,z5,z6])],[(0,[z0,z19,z25,z3,z4,z5,z6]),(0,[z58,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z16,z4,z5,z6,z99]),(0,[z0,z210,z1,z3,z127,z5,z6]),(0,[z0,z36,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z180])],[(0,[z0,z1,z3,z4,z5,z211,z6]),(0,[z0,z210,z1,z3,z4,z5,z6]),(0,[z0,z1,z128,z3,z4,z5,z6]),(0,[z0,z66,z1,z3,z4,z5,z13])],[(1,[z95,z1,z3,z4,z20,z6]),(0,[z212,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z213,z5,z6]),(0,[z0,z1,z214,z4,z5,z6,z14])]],
   [[(0,[z0,z215,z1,z3,z4,z5,z6]),(0,[z0,z49,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z121,z6]),(0,[z0,z1,z111,z3,z4,z5,z6]),(0,[z0,z1,z3,z173,z4,z5,z13])],[(0,[z216,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z217,z4,z5,z6]),(0,[z0,z218,z1,z3,z4,z5,z6]),(0,[z219,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z220,z6]),(0,[z0,z1,z3,z4,z5,z221,z6]),(0,[z0,z66,z1,z222,z4,z5,z6])],[(0,[z0,z223,z1,z3,z4,z5,z6]),(0,[z31,z0,z19,z3,z4,z5,z6]),(0,[z0,z224,z1,z3,z4,z5,z6]),(0,[z0,z104,z1,z161,z4,z5,z6]),(0,[z0,z1,z4,z5,z101,z6,z14])],[(0,[z0,z1,z3,z225,z4,z5,z6]),(0,[z0,z1,z25,z3,z4,z5,z6]),(0,[z0,z1,z16,z25,z4,z5,z6]),(0,[z0,z43,z1,z73,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z6,z12]),(0,[z0,z1,z3,z226,z4,z5,z6])],[(1,[z0,z1,z3,z97,z5,z6]),(0,[z0,z1,z4,z5,z6,z99,z14]),(0,[z0,z1,z79,z128,z3,z5,z6]),(1,[z0,z1,z227,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z228]),(0,[z0,z1,z3,z4,z229,z5,z6]),(0,[z0,z230,z1,z3,z4,z5,z6]),(1,[z0,z134,z1,z3,z4,z6]),(0,[z0,z19,z16,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z6,z12]),(0,[z151,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z16,z4,z5,z101]),(1,[z0,z1,z3,z76,z5,z6])],[(0,[z55,z0,z1,z4,z5,z6,z14]),(0,[z84,z0,z1,z3,z4,z5,z6]),(0,[z52,z0,z36,z1,z3,z5,z6]),(0,[z0,z19,z3,z4,z8,z5,z6]),(0,[z0,z1,z3,z4,z5,z231,z6]),(0,[z1,z3,z4,z5,z6,z232,z27]),(0,[z0,z1,z3,z4,z70,z6,z140])]],
   [[],[(0,[z0,z233,z1,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z22,z5,z6]),(0,[z0,z19,z3,z4,z18,z5,z6]),(0,[z74,z0,z19,z3,z4,z5,z6]),(0,[z0,z1,z234,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z235,z5,z6]),(0,[z0,z1,z69,z3,z4,z5,z6]),(0,[z0,z1,z236,z3,z4,z5,z6]),(0,[z0,z100,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z23,z6]),(0,[z0,z1,z3,z4,z5,z6,z237]),(0,[z0,z1,z3,z17,z4,z18,z6])],[(0,[z0,z238,z1,z3,z4,z5,z6]),(0,[z239,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z240,z3,z4,z5,z6]),(0,[z0,z241,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z22,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z12]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z243,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z244,z6])],[(0,[z55,z1,z137,z3,z4,z5,z6]),(0,[z0,z1,z245,z3,z4,z5,z6]),(0,[z0,z1,z246,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z32,z6,z247]),(0,[z0,z1,z3,z4,z98,z127,z6]),(0,[z0,z1,z3,z4,z5,z248,z6]),(0,[z0,z19,z1,z4,z5,z6,z14])],[(0,[z249,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z21,z4,z5,z6,z14]),(0,[z0,z1,z4,z5,z250,z6,z14]),(0,[z0,z1,z3,z4,z251,z5,z6])],[(0,[z0,z1,z3,z4,z8,z5,z6]),(0,[z0,z252,z1,z3,z4,z5,z6]),(0,[z96,z0,z1,z4,z5,z6,z14]),(0,[z0,z186,z1,z3,z4,z5,z6]),(1,[z0,z100,z3,z4,z33,z6]),(0,[z0,z1,z3,z222,z4,z5,z6]),(0,[z0,z1,z253,z3,z4,z5,z6])],[(0,[z0,z1,z3,z254,z4,z5,z6]),(0,[z0,z1,z255,z3,z4,z5,z6]),(0,[z0,z19,z155,z3,z4,z5,z6]),(0,[z78,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z16,z128,z4,z5,z6]),(0,[z0,z3,z17,z4,z256,z5,z6])]],
   [[(0,[z7,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z257,z6]),(0,[z0,z258,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z22,z5,z6]),(0,[z0,z1,z227,z3,z4,z5,z6])],[(0,[z0,z259,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z260,z5,z6]),(0,[z0,z1,z3,z261,z4,z5,z6])],[(0,[z0,z262,z1,z3,z4,z5,z6]),(0,[z0,z1,z263,z3,z4,z5,z6]),(0,[z0,z264,z1,z3,z4,z5,z6]),(0,[z0,z1,z128,z3,z117,z5,z6]),(0,[z0,z1,z4,z117,z5,z6,z14]),(0,[z0,z265,z1,z3,z4,z5,z6]),(0,[z0,z1,z266,z3,z4,z5,z6])],[(0,[z0,z49,z1,z3,z267,z5,z6]),(0,[z0,z1,z3,z4,z5,z268,z6]),(0,[z84,z0,z104,z1,z4,z5,z6]),(0,[z0,z1,z3,z269,z4,z5,z6]),(0,[z270,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z271,z5,z6]),(0,[z0,z3,z4,z33,z5,z272,z6]),(0,[z0,z1,z4,z5,z6,z12,z14]),(0,[z273,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z274,z3,z4,z5,z6]),(0,[z0,z275,z1,z3,z4,z5,z6]),(0,[z276,z0,z1,z3,z4,z5,z6]),(1,[z0,z277,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z278,z6]),(0,[z1,z25,z3,z279,z4,z5,z6]),(0,[z0,z280,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z281,z4,z5,z6]),(0,[z0,z120,z3,z4,z33,z5,z6])],[(0,[z282,z0,z1,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z18,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z283])],[(1,[z284,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z285,z6]),(0,[z0,z286,z1,z3,z4,z5,z6]),(0,[z0,z277,z3,z17,z4,z5,z6])],[(0,[z0,z287,z1,z3,z4,z5,z6]),(0,[z96,z0,z288,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z162,z6]),(0,[z0,z210,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z289,z4,z5,z6]),(0,[z0,z290,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z122]),(0,[z0,z1,z291,z16,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z292,z4,z5,z6]),(0,[z0,z167,z1,z4,z5,z6,z14]),(0,[z293,z0,z19,z3,z4,z5,z6]),(1,[z0,z19,z3,z4,z45,z6])],[(0,[z294,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z295]),(0,[z96,z1,z3,z4,z131,z5,z6]),(0,[z0,z19,z3,z4,z5,z6,z140]),(0,[z0,z1,z16,z4,z5,z45,z6])],[(0,[z293,z0,z1,z3,z4,z5,z6]),(0,[z84,z0,z1,z279,z4,z5,z6]),(0,[z0,z1,z3,z4,z296,z5,z6]),(0,[z297,z0,z1,z3,z4,z5,z6]),(0,[z298,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z299,z4,z5,z6])],[(1,[z0,z28,z69,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z6,z140]),(0,[z300,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z301,z6]),(0,[z0,z11,z1,z4,z5,z6,z14])],[(0,[z0,z1,z137,z16,z4,z5,z6]),(0,[z0,z302,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z13,z6]),(0,[z303,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z222,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z304])],[(0,[z305,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z306,z3,z4,z5,z6]),(0,[z7,z0,z1,z4,z5,z6,z14]),(0,[z0,z307,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z20,z6,z14]),(0,[z0,z1,z3,z4,z5,z6,z308]),(0,[z0,z1,z3,z4,z5,z6,z309]),(0,[z0,z19,z3,z4,z5,z6,z27]),(0,[z0,z1,z3,z310,z4,z5,z6]),(1,[z0,z11,z3,z4,z5,z12]),(0,[z0,z1,z3,z4,z5,z6,z311])],[(0,[z31,z0,z3,z4,z33,z5,z6]),(0,[z0,z19,z3,z17,z4,z5,z6])],[(0,[z0,z19,z49,z3,z4,z5,z6]),(0,[z0,z312,z1,z3,z4,z5,z6]),(0,[z0,z19,z161,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z6,z27])]],
   [[(0,[z0,z1,z79,z4,z117,z5,z6]),(0,[z0,z1,z79,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z140])],[(0,[z49,z1,z137,z3,z4,z5,z6]),(0,[z313,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z314,z3,z4,z5,z6]),(0,[z0,z315,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z316,z4,z5,z6]),(0,[z78,z0,z1,z16,z4,z5,z6]),(0,[z0,z155,z1,z3,z4,z5,z6]),(0,[z0,z36,z1,z3,z17,z5,z6]),(1,[z0,z1,z4,z5,z133,z6]),(0,[z0,z1,z3,z4,z5,z13,z6])],[(0,[z0,z57,z1,z3,z5,z20,z6]),(0,[z0,z1,z3,z317,z4,z5,z6]),(0,[z0,z194,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z70,z6,z180])],[(0,[z0,z1,z318,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z32,z6]),(0,[z0,z1,z16,z4,z127,z5,z6]),(0,[z0,z3,z4,z33,z5,z319,z6]),(0,[z0,z1,z3,z5,z13,z6,z27]),(0,[z0,z320,z1,z3,z4,z5,z6]),(0,[z0,z321,z1,z3,z4,z5,z6])],[(0,[z183,z0,z1,z3,z4,z5,z99]),(0,[z74,z0,z3,z4,z33,z5,z6]),(0,[z0,z66,z1,z209,z4,z5,z6]),(0,[z0,z66,z1,z3,z4,z5,z27]),(0,[z0,z1,z3,z4,z5,z6,z27])],[(0,[z0,z3,z4,z33,z5,z32,z6]),(0,[z0,z322,z1,z3,z4,z5,z6]),(0,[z0,z1,z92,z4,z5,z121,z6]),(0,[z0,z323,z1,z3,z4,z5,z6])],[(0,[z183,z0,z19,z3,z4,z5,z6]),(0,[z0,z1,z3,z324,z4,z5,z6]),(0,[z0,z19,z36,z3,z4,z5,z6]),(0,[z0,z120,z1,z16,z4,z5,z6]),(1,[z0,z1,z3,z325,z5,z6]),(0,[z326,z0,z1,z3,z4,z5,z6]),(0,[z0,z327,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z173,z4,z5,z27])],[(0,[z0,z1,z3,z328,z4,z5,z6]),(0,[z0,z1,z3,z4,z131,z105,z6]),(1,[z58,z1,z3,z4,z5,z99])]],
   [[(0,[z52,z0,z1,z3,z21,z5,z6]),(0,[z183,z0,z1,z3,z4,z5,z6]),(0,[z329,z0,z1,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z330,z6]),(1,[z0,z3,z4,z5,z331,z6]),(0,[z0,z1,z3,z4,z332,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z333]),(0,[z7,z1,z3,z26,z4,z5,z6]),(0,[z0,z210,z1,z16,z4,z5,z6]),(0,[z0,z334,z19,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z32,z6]),(0,[z0,z210,z167,z3,z4,z5,z6]),(0,[z0,z100,z1,z3,z4,z33,z6])],[(0,[z0,z335,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z336,z4,z5,z6]),(0,[z284,z0,z1,z3,z4,z5,z6]),(0,[z0,z337,z1,z3,z4,z5,z6]),(1,[z0,z210,z3,z21,z5,z6]),(0,[z0,z210,z120,z3,z4,z5,z6]),(0,[z0,z334,z1,z3,z4,z5,z6]),(0,[z0,z1,z338,z3,z4,z5,z6])],[(0,[z96,z0,z1,z3,z4,z20,z6]),(1,[z0,z1,z339,z4,z5,z6]),(0,[z58,z1,z3,z4,z5,z6,z99]),(0,[z0,z3,z4,z340,z33,z5,z6]),(0,[z216,z0,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z331,z6])],[(0,[z0,z1,z3,z4,z5,z6,z341]),(0,[z0,z1,z3,z4,z5,z6,z342]),(0,[z0,z1,z3,z4,z343,z5,z6]),(1,[z0,z265,z3,z4,z5,z6])],[(0,[z344,z0,z1,z3,z4,z5,z6]),(0,[z29,z0,z49,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z345,z6])],[(0,[z0,z1,z3,z346,z4,z5,z6]),(0,[z0,z19,z1,z3,z4,z131,z6]),(0,[z74,z183,z0,z1,z3,z4,z5]),(0,[z0,z69,z3,z4,z33,z5,z6]),(0,[z0,z1,z291,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z330,z6]),(0,[z0,z19,z1,z3,z4,z70,z6]),(0,[z0,z120,z1,z3,z4,z5,z121]),(1,[z0,z1,z161,z4,z22,z6]),(0,[z0,z1,z16,z4,z105,z5,z6])]],
   [[(1,[z0,z347,z1,z4,z5,z6]),(0,[z31,z0,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z173,z8,z5,z6]),(1,[z0,z1,z317,z4,z5,z6]),(0,[z0,z1,z339,z3,z4,z5,z6]),(0,[z0,z280,z1,z3,z5,z6,z99]),(0,[z0,z348,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z349,z6])],[(0,[z96,z0,z1,z3,z4,z131,z6]),(0,[z0,z264,z1,z3,z4,z6,z12]),(0,[z0,z1,z4,z5,z6,z14,z140]),(0,[z0,z1,z16,z4,z5,z70,z6])],[(0,[z0,z19,z66,z3,z4,z5,z6]),(0,[z0,z1,z129,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z350]),(0,[z0,z351,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z14,z352]),(0,[z0,z66,z1,z3,z173,z5,z6]),(0,[z0,z1,z3,z4,z353,z5,z6])],[(0,[z354,z0,z1,z3,z4,z5,z6]),(0,[z183,z1,z3,z4,z5,z32,z6]),(0,[z0,z1,z355,z3,z4,z5,z6]),(1,[z0,z16,z4,z33,z5,z6]),(0,[z300,z0,z3,z4,z33,z5,z6]),(0,[z0,z356,z1,z4,z5,z6,z14])],[(0,[z357,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z131,z5,z6]),(0,[z358,z0,z1,z3,z4,z5,z6]),(0,[z0,z359,z1,z3,z4,z5,z6]),(0,[z0,z1,z69,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z360]),(0,[z0,z1,z4,z5,z6,z14,z27])],[(0,[z0,z361,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z362,z6]),(0,[z0,z28,z1,z79,z4,z5,z6]),(0,[z0,z363,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z108,z4,z5,z6]),(0,[z242,z0,z1,z16,z4,z5,z6]),(0,[z74,z0,z1,z16,z4,z5,z6]),(0,[z0,z277,z1,z3,z4,z5,z6])],[(0,[z55,z0,z19,z3,z4,z5,z6]),(0,[z0,z364,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z365,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z366,z6]),(1,[z0,z3,z196,z4,z5,z6]),(0,[z0,z87,z161,z3,z4,z5,z6]),(0,[z0,z1,z161,z4,z5,z6,z14])]],
   [[(0,[z0,z19,z3,z4,z5,z45,z6]),(0,[z0,z36,z100,z1,z3,z4,z6]),(0,[z0,z1,z16,z4,z33,z5,z6]),(0,[z0,z1,z79,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z117,z5,z6]),(0,[z0,z1,z16,z16,z4,z5,z6]),(0,[z74,z0,z1,z3,z4,z5,z70])],[(0,[z0,z1,z3,z4,z5,z6,z367]),(0,[z183,z0,z1,z3,z4,z5,z32]),(0,[z0,z368,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z152]),(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z369]),(0,[z0,z1,z3,z4,z370,z5,z6])],[(0,[z0,z1,z3,z371,z4,z5,z6]),(0,[z0,z1,z3,z4,z131,z5,z6]),(0,[z183,z0,z1,z3,z4,z105,z5]),(0,[z0,z1,z3,z73,z4,z5,z6]),(0,[z0,z19,z3,z372,z4,z5,z6]),(1,[z74,z0,z19,z3,z4,z6]),(0,[z0,z19,z36,z1,z3,z4,z6]),(0,[z0,z155,z3,z4,z33,z5,z6]),(0,[z0,z104,z1,z3,z4,z23,z6])],[(0,[z0,z1,z3,z26,z4,z5,z6]),(0,[z74,z0,z1,z3,z4,z105,z6]),(0,[z0,z1,z3,z4,z5,z373,z6])],[(0,[z0,z1,z3,z4,z5,z162,z6]),(0,[z0,z1,z3,z4,z5,z6,z374])],[(0,[z0,z56,z1,z137,z4,z5,z6]),(0,[z0,z375,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z376]),(0,[z0,z1,z3,z377,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z6,z378]),(0,[z0,z1,z3,z18,z5,z6,z27])],[(0,[z0,z1,z3,z379,z4,z5,z6]),(0,[z52,z0,z1,z3,z8,z5,z6]),(0,[z96,z0,z19,z3,z4,z5,z6]),(0,[z0,z11,z1,z3,z4,z5,z121]),(0,[z0,z1,z3,z4,z5,z6,z380]),(1,[z0,z264,z1,z3,z4,z6]),(0,[z0,z381,z1,z3,z4,z5,z6]),(0,[z382,z0,z1,z3,z4,z5,z6]),(0,[z0,z104,z1,z4,z5,z6,z14])],[(0,[z74,z0,z1,z3,z4,z6,z140])]],
   [[(0,[z0,z1,z3,z383,z4,z5,z6]),(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z384,z4,z5,z6]),(0,[z0,z1,z3,z4,z340,z5,z6]),(0,[z78,z0,z36,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z385,z6]),(0,[z0,z1,z3,z4,z5,z386,z6]),(0,[z0,z36,z1,z3,z173,z5,z6])],[(0,[z183,z0,z3,z4,z33,z5,z6]),(0,[z0,z3,z4,z127,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z387,z6]),(0,[z388,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z123])],[(1,[z55,z137,z3,z4,z5,z6]),(0,[z0,z1,z3,z389,z4,z5,z6]),(0,[z0,z1,z3,z390,z4,z5,z6]),(0,[z0,z1,z4,z5,z32,z6,z14]),(0,[z0,z1,z3,z4,z391,z5,z6]),(0,[z0,z120,z3,z4,z127,z5,z6]),(0,[z0,z19,z3,z4,z5,z101,z6]),(0,[z0,z161,z3,z4,z33,z5,z6]),(0,[z0,z3,z17,z4,z33,z5,z6]),(0,[z0,z392,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z393,z4,z5,z6])],[(1,[z31,z1,z279,z4,z5,z6]),(0,[z95,z1,z3,z4,z5,z20,z6]),(0,[z0,z1,z3,z4,z5,z394,z20]),(0,[z0,z134,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z395,z4,z5,z6]),(0,[z0,z11,z1,z3,z396,z5,z6]),(0,[z0,z1,z3,z173,z5,z13,z6])],[(0,[z0,z1,z3,z397,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z101,z6]),(0,[z0,z3,z4,z5,z121,z6,z12]),(0,[z0,z1,z3,z4,z398,z5,z6]),(0,[z0,z1,z16,z4,z5,z6,z6]),(0,[z0,z66,z1,z3,z5,z6,z27])],[(0,[z0,z1,z399,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z400,z6]),(1,[z0,z3,z4,z229,z5,z6]),(0,[z0,z1,z4,z131,z5,z6,z14]),(0,[z0,z401,z1,z3,z4,z5,z6]),(0,[z402,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z403,z5,z6]),(0,[z0,z1,z173,z4,z5,z6,z14]),(0,[z404,z0,z1,z3,z4,z5,z6])],[(0,[z0,z28,z1,z73,z4,z5,z6]),(0,[z0,z1,z16,z173,z4,z5,z6])],[(0,[z29,z49,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z405,z4,z5,z6]),(0,[z0,z28,z69,z3,z4,z5,z6]),(0,[z0,z210,z3,z21,z4,z5,z6])]],
   [[(0,[z31,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z406,z5,z6]),(0,[z407,z0,z1,z3,z4,z5,z6])],[(0,[z0,z3,z4,z8,z33,z5,z6]),(0,[z58,z0,z1,z339,z4,z5,z6]),(0,[z0,z1,z3,z86,z4,z5,z6]),(0,[z0,z1,z3,z408,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z101,z6])],[(0,[z409,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z72,z4,z5,z6]),(0,[z0,z1,z72,z4,z5,z32,z6]),(0,[z0,z167,z1,z3,z4,z5,z6]),(0,[z0,z1,z355,z4,z127,z5,z6]),(0,[z0,z1,z3,z4,z403,z5,z6]),(0,[z0,z1,z4,z5,z6,z6,z14]),(0,[z0,z1,z3,z4,z5,z410,z6])],[(0,[z0,z411,z1,z3,z4,z5,z6]),(0,[z0,z3,z279,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z412,z5,z6]),(0,[z0,z1,z3,z4,z5,z413,z6]),(0,[z0,z1,z3,z4,z5,z414,z6]),(0,[z0,z1,z3,z4,z415,z5,z6]),(0,[z404,z1,z3,z4,z5,z6,z27])],[(0,[z0,z1,z3,z4,z416,z5,z6]),(0,[z0,z155,z1,z16,z4,z5,z6])],[(0,[z7,z0,z19,z3,z4,z5,z6]),(1,[z0,z1,z3,z417,z5,z6]),(0,[z58,z0,z1,z317,z4,z5,z6]),(0,[z418,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z419,z33,z5,z6]),(0,[z0,z11,z1,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z117,z5,z6])],[(0,[z58,z52,z1,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z127,z5,z6]),(0,[z0,z1,z3,z4,z420,z5,z6]),(0,[z0,z1,z421,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z232]),(0,[z74,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z105,z5,z140])],[(0,[z0,z422,z1,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z4,z5,z6]),(0,[z423,z0,z1,z3,z4,z5,z6]),(0,[z0,z424,z1,z3,z4,z5,z6]),(0,[z0,z1,z425,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z426,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z427]),(1,[z0,z19,z4,z5,z6,z14]),(0,[z0,z1,z16,z3,z4,z5,z6]),(0,[z0,z428,z1,z3,z4,z5,z6]),(0,[z0,z429,z3,z4,z5,z6,z140])],[(0,[z0,z1,z3,z4,z430,z5,z6]),(0,[z52,z0,z1,z3,z5,z13,z6]),(0,[z0,z1,z3,z4,z5,z6,z247]),(0,[z0,z43,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z431,z5,z6]),(0,[z0,z19,z3,z4,z5,z46,z6]),(0,[z0,z1,z17,z4,z5,z6,z14]),(0,[z0,z36,z1,z3,z5,z6,z27]),(0,[z0,z1,z3,z4,z5,z6,z432]),(0,[z0,z191,z1,z3,z4,z5,z6])],[(0,[z55,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z433,z4,z5,z6]),(0,[z0,z3,z434,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z435]),(1,[z0,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z436,z5,z6]),(1,[z0,z429,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z437,z5,z6]),(0,[z58,z74,z0,z1,z3,z4,z5]),(0,[z183,z0,z1,z16,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z46,z6]),(0,[z0,z1,z3,z4,z5,z438,z6]),(0,[z0,z1,z3,z4,z439,z5,z6]),(0,[z0,z1,z3,z4,z18,z5,z6])],[(0,[z31,z0,z104,z1,z4,z5,z6]),(0,[z0,z128,z3,z4,z33,z5,z6])],[(0,[z0,z1,z3,z417,z5,z20,z6]),(0,[z0,z19,z43,z3,z4,z5,z6]),(0,[z0,z11,z1,z338,z4,z5,z6]),(0,[z0,z1,z128,z4,z22,z5,z6]),(0,[z0,z1,z4,z5,z6,z14,z14])],[(0,[z0,z1,z3,z4,z5,z440,z6]),(0,[z52,z0,z66,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z417,z5,z6]),(0,[z0,z1,z3,z4,z441,z5,z6]),(0,[z0,z1,z3,z4,z442,z5,z6]),(0,[z0,z19,z3,z4,z443,z5,z6]),(0,[z0,z87,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z133,z6]),(0,[z0,z66,z265,z3,z4,z5,z6]),(0,[z0,z1,z3,z444,z4,z5,z6])],[(0,[z95,z0,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z445,z5,z6]),(0,[z0,z1,z3,z21,z173,z5,z6]),(0,[z0,z19,z1,z3,z17,z4,z6]),(1,[z0,z1,z86,z4,z5,z6]),(0,[z0,z446,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z447,z6])]],
   [[(0,[z0,z49,z3,z4,z5,z6,z12])],[(0,[z96,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z448,z3,z4,z5,z6]),(0,[z0,z1,z199,z3,z4,z5,z6]),(0,[z449,z0,z1,z3,z4,z5,z6])],[(0,[z0,z450,z1,z3,z4,z5,z6]),(1,[z0,z104,z1,z4,z23,z6])],[(0,[z31,z0,z1,z279,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z272,z6]),(0,[z0,z1,z3,z325,z5,z23,z6]),(1,[z0,z1,z3,z173,z5,z13])],[(0,[z0,z1,z3,z4,z5,z451,z6]),(1,[z0,z1,z3,z108,z5,z6])],[(0,[z452,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z453,z6]),(0,[z0,z1,z3,z4,z443,z5,z6]),(0,[z0,z100,z1,z3,z4,z45,z6]),(0,[z0,z454,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z455,z5,z6]),(0,[z0,z1,z4,z105,z5,z6,z14])],[(0,[z29,z0,z1,z4,z5,z6,z14]),(0,[z84,z0,z1,z4,z22,z5,z6]),(0,[z0,z1,z456,z3,z4,z5,z6])],[(0,[z0,z19,z3,z4,z5,z6,z99]),(1,[z0,z1,z4,z5,z6,z247]),(0,[z0,z1,z3,z4,z5,z457,z6]),(0,[z0,z1,z3,z4,z458,z5,z6]),(0,[z459,z0,z19,z3,z4,z5,z6])]],
   [[(0,[z460,z0,z1,z3,z4,z5,z6]),(0,[z0,z461,z1,z3,z4,z5,z6]),(0,[z74,z0,z19,z1,z3,z4,z6]),(0,[z0,z462,z1,z3,z4,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z463,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z73,z4,z33,z5,z6]),(0,[z459,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z464]),(0,[z0,z1,z16,z4,z251,z5,z6]),(0,[z0,z465,z1,z3,z4,z5,z6])],[],[(0,[z0,z1,z16,z279,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z466]),(0,[z467,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z468,z4,z5,z6]),(0,[z0,z167,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z469,z6])],[(0,[z55,z0,z1,z16,z4,z5,z6]),(0,[z0,z120,z137,z3,z4,z5,z6]),(0,[z0,z1,z16,z3,z4,z5,z101]),(0,[z0,z1,z3,z470,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z471,z6]),(0,[z472,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z352]),(0,[z0,z19,z3,z473,z4,z5,z6]),(0,[z0,z19,z3,z173,z4,z5,z6]),(0,[z0,z1,z3,z474,z4,z5,z6]),(0,[z0,z475,z1,z16,z4,z5,z6])],[(0,[z0,z1,z3,z4,z98,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z476]),(0,[z0,z79,z3,z4,z33,z5,z6]),(0,[z0,z11,z3,z4,z33,z5,z6]),(0,[z0,z477,z1,z3,z4,z5,z6]),(0,[z0,z356,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z478]),(0,[z0,z1,z479,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z480,z5,z6]),(0,[z481,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z425,z3,z4,z5,z6]),(0,[z0,z1,z3,z482,z4,z5,z6]),(0,[z78,z0,z1,z79,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z350])]],
   [[(0,[z483,z0,z1,z3,z4,z5,z6]),(0,[z7,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z16,z21,z4,z5,z6]),(0,[z0,z1,z3,z21,z5,z6,z27]),(0,[z0,z1,z3,z17,z4,z5,z6])],[(0,[z0,z484,z1,z3,z4,z5,z6]),(0,[z0,z210,z1,z3,z21,z5,z6]),(0,[z0,z19,z1,z16,z4,z5,z6]),(0,[z0,z1,z161,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z485,z23,z6]),(0,[z0,z36,z1,z3,z4,z46,z6]),(0,[z0,z1,z3,z4,z5,z486,z6])],[(0,[z0,z487,z1,z3,z4,z5,z6]),(0,[z0,z488,z1,z3,z4,z5,z6]),(0,[z0,z1,z489,z3,z4,z5,z6])],[(0,[z96,z0,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z319,z6]),(0,[z0,z1,z3,z490,z4,z5,z6])],[(0,[z491,z0,z1,z3,z4,z5,z6]),(0,[z0,z149,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z492,z6]),(0,[z0,z1,z3,z4,z5,z493,z6]),(0,[z0,z19,z3,z4,z5,z23,z6]),(0,[z0,z1,z3,z4,z5,z494,z6]),(1,[z0,z495,z3,z4,z5,z6])],[(0,[z0,z19,z1,z3,z4,z20,z6]),(0,[z0,z104,z1,z4,z5,z23,z6]),(0,[z0,z496,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z497,z5,z6]),(0,[z96,z0,z181,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z131,z6,z140]),(0,[z0,z498,z1,z3,z4,z5,z6])],[(1,[z29,z49,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z20,z6]),(0,[z58,z0,z1,z4,z5,z6,z14]),(0,[z0,z499,z1,z3,z4,z5,z6]),(0,[z0,z1,z500,z3,z4,z5,z6]),(0,[z0,z1,z4,z455,z5,z6,z14]),(0,[z501,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z173,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z502]),(0,[z0,z1,z3,z4,z5,z6,z503])],[(0,[z0,z1,z3,z4,z5,z504,z6]),(0,[z0,z505,z1,z3,z4,z5,z6]),(1,[z84,z1,z25,z4,z5,z6]),(0,[z0,z1,z3,z4,z506,z5,z6]),(0,[z0,z1,z35,z3,z4,z5,z6]),(0,[z0,z1,z3,z434,z4,z5,z6]),(0,[z0,z507,z1,z3,z4,z5,z6]),(1,[z0,z1,z77,z4,z5,z6])],[(0,[z0,z347,z1,z137,z4,z5,z6]),(1,[z0,z1,z3,z508,z5,z6]),(0,[z84,z0,z43,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z509,z6]),(0,[z0,z1,z3,z510,z4,z5,z6]),(0,[z511,z0,z1,z3,z4,z5,z6]),(0,[z0,z104,z1,z128,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z512])],[(1,[z0,z19,z3,z4,z131,z6]),(1,[z0,z19,z3,z4,z70,z6]),(0,[z0,z120,z3,z4,z5,z121,z6])],[(0,[z0,z513,z1,z3,z4,z5,z6])],[(0,[z0,z1,z514,z3,z4,z5,z6]),(0,[z0,z1,z3,z515,z4,z5,z6]),(0,[z0,z167,z1,z16,z4,z5,z6]),(0,[z0,z516,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z517]),(0,[z78,z0,z1,z79,z3,z5,z6]),(0,[z0,z1,z3,z325,z4,z5,z6]),(0,[z0,z518,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z519]),(0,[z0,z1,z3,z173,z18,z5,z6])],[(0,[z520,z0,z1,z3,z4,z5,z6]),(0,[z521,z0,z1,z3,z4,z5,z6]),(0,[z522,z0,z1,z3,z4,z5,z6]),(0,[z452,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z123])],[(0,[z0,z523,z1,z3,z4,z5,z6])]],
   [[(1,[z0,z280,z1,z3,z5,z6]),(0,[z0,z11,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z524,z5,z6]),(0,[z0,z155,z1,z3,z4,z5,z101]),(0,[z525,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z526,z6]),(1,[z0,z1,z355,z4,z5,z6]),(0,[z0,z19,z11,z3,z4,z5,z6]),(0,[z54,z0,z1,z4,z5,z6,z14]),(0,[z0,z1,z421,z16,z4,z5,z6]),(1,[z0,z40,z3,z4,z5,z6]),(0,[z0,z1,z3,z527,z4,z5,z6])],[(0,[z7,z0,z1,z16,z4,z5,z6]),(0,[z95,z0,z1,z3,z4,z131,z6]),(0,[z0,z1,z3,z4,z5,z528,z6]),(0,[z0,z19,z210,z3,z4,z5,z6]),(0,[z0,z11,z120,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z529,z6]),(0,[z0,z1,z3,z4,z5,z530,z6]),(0,[z0,z531,z1,z4,z5,z6,z14]),(0,[z0,z66,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z532,z4,z5,z6]),(0,[z0,z533,z1,z3,z4,z5,z6]),(0,[z0,z534,z1,z3,z4,z5,z6]),(1,[z0,z1,z479,z4,z5,z6])],[(0,[z55,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z535,z5,z6]),(0,[z536,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z537,z6])],[(0,[z538,z0,z1,z3,z4,z5,z6]),(0,[z539,z0,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z540,z5,z6]),(0,[z0,z3,z4,z33,z5,z45,z6]),(0,[z0,z541,z1,z3,z4,z5,z6]),(0,[z0,z475,z1,z3,z4,z5,z6]),(1,[z0,z36,z1,z3,z46,z6])],[(0,[z0,z1,z542,z3,z4,z5,z6]),(0,[z52,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z543,z6]),(0,[z0,z1,z3,z4,z5,z6,z544])],[(0,[z0,z1,z3,z4,z545,z5,z6]),(0,[z546,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z547]),(0,[z0,z19,z19,z3,z4,z5,z6]),(0,[z0,z548,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z549,z6]),(0,[z0,z49,z1,z3,z508,z5,z6]),(0,[z0,z3,z4,z550,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z551,z6]),(0,[z0,z1,z4,z5,z23,z6,z14])],[(0,[z0,z552,z1,z3,z4,z5,z6]),(0,[z0,z210,z3,z4,z5,z6,z12]),(0,[z0,z19,z1,z3,z4,z5,z6]),(0,[z0,z1,z128,z3,z18,z5,z6]),(0,[z553,z0,z1,z3,z4,z5,z6]),(0,[z74,z0,z1,z146,z4,z5,z6]),(0,[z0,z554,z1,z3,z4,z5,z6])],[(0,[z0,z555,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z45,z6]),(0,[z0,z3,z4,z33,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z556,z6]),(0,[z0,z1,z3,z4,z5,z6,z557])],[(0,[z52,z0,z1,z3,z18,z5,z6]),(0,[z0,z43,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z550,z5,z6]),(0,[z0,z1,z3,z4,z5,z558,z6])],[(0,[z0,z559,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z105,z20,z6]),(0,[z0,z28,z1,z128,z4,z5,z6]),(0,[z0,z1,z3,z372,z4,z5,z6])],[(0,[z0,z43,z1,z128,z4,z5,z6]),(0,[z0,z19,z3,z4,z127,z5,z6]),(0,[z560,z0,z1,z3,z4,z5,z6])],[(0,[z0,z43,z1,z69,z4,z5,z6])],[(0,[z561,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z562,z5,z6]),(1,[z0,z1,z3,z4,z6,z154]),(0,[z0,z1,z3,z4,z563,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z14]),(0,[z0,z564,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z565,z5,z6]),(0,[z0,z1,z3,z566,z4,z5,z6]),(0,[z0,z3,z4,z229,z5,z20,z6]),(0,[z0,z1,z3,z567,z5,z23,z6]),(0,[z0,z36,z1,z4,z5,z6,z14])],[(0,[z74,z0,z100,z1,z3,z4,z6]),(0,[z0,z1,z128,z4,z5,z6,z14]),(1,[z0,z1,z16,z4,z5,z14]),(0,[z0,z1,z3,z4,z105,z70,z6])],[(0,[z0,z1,z3,z4,z419,z5,z6]),(0,[z0,z568,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z197,z14])],[(0,[z0,z1,z3,z4,z5,z6,z569]),(0,[z0,z1,z3,z4,z570,z5,z6]),(0,[z52,z0,z1,z4,z5,z6,z14]),(1,[z0,z1,z4,z540,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z571]),(0,[z0,z572,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z147])],[(0,[z0,z3,z26,z4,z33,z5,z6]),(1,[z0,z1,z3,z4,z5,z394]),(0,[z0,z1,z3,z573,z4,z5,z6]),(0,[z0,z167,z1,z3,z127,z5,z6]),(0,[z0,z1,z3,z4,z574,z5,z6]),(0,[z0,z1,z3,z4,z5,z575,z6]),(0,[z0,z1,z3,z4,z5,z485,z6]),(0,[z74,z0,z1,z227,z4,z5,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z576,z6]),(0,[z577,z0,z1,z3,z4,z5,z6])],[(0,[z29,z0,z19,z3,z4,z5,z6]),(0,[z0,z158,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z131,z5,z6]),(0,[z0,z1,z16,z73,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z578]),(0,[z0,z1,z3,z4,z5,z579,z6])],[(0,[z0,z137,z3,z4,z33,z5,z6]),(0,[z0,z580,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z581,z6]),(0,[z0,z1,z16,z26,z4,z5,z6]),(0,[z0,z582,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z6,z62]),(0,[z583,z0,z1,z3,z4,z5,z6]),(0,[z584,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z79,z4,z22,z5,z6])]],
   [[(0,[z0,z585,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z586,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z587]),(0,[z0,z588,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z589,z5,z6]),(0,[z0,z167,z3,z4,z127,z5,z6]),(0,[z0,z19,z3,z4,z105,z5,z6]),(0,[z0,z16,z3,z4,z33,z5,z6]),(0,[z0,z1,z590,z16,z4,z5,z6])],[(0,[z84,z0,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z591,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z592,z6]),(1,[z404,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z593,z5,z6]),(0,[z0,z28,z1,z4,z5,z6,z14]),(0,[z0,z1,z594,z3,z4,z5,z6]),(0,[z0,z1,z4,z127,z5,z6,z14]),(0,[z0,z19,z3,z4,z5,z70,z6]),(0,[z0,z1,z3,z4,z5,z595,z6]),(0,[z0,z3,z4,z33,z105,z5,z6])],[(0,[z0,z347,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z596]),(1,[z0,z1,z3,z4,z535,z6]),(0,[z0,z1,z3,z597,z4,z5,z6]),(0,[z0,z598,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z599,z5,z6])],[(0,[z0,z1,z3,z4,z5,z600,z6]),(0,[z0,z601,z1,z3,z4,z5,z6]),(0,[z0,z602,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z603]),(0,[z0,z1,z3,z4,z5,z604,z6]),(0,[z0,z100,z1,z4,z5,z6,z14]),(0,[z0,z1,z4,z5,z6,z578,z14])],[(0,[z0,z1,z3,z4,z605,z5,z6]),(0,[z606,z0,z1,z3,z4,z5,z6]),(0,[z607,z0,z1,z3,z4,z5,z6]),(0,[z608,z0,z1,z3,z4,z5,z6])],[(0,[z0,z3,z4,z33,z5,z609,z6]),(0,[z0,z1,z16,z4,z5,z121,z6])]],
   [[(1,[z0,z158,z1,z4,z5,z6]),(1,[z0,z552,z3,z4,z5,z6]),(0,[z0,z3,z4,z18,z33,z5,z6]),(0,[z0,z1,z610,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z105,z5,z6])],[(0,[z0,z120,z49,z3,z4,z5,z6]),(0,[z7,z0,z36,z1,z3,z5,z6]),(1,[z0,z1,z4,z5,z6,z147]),(0,[z0,z161,z3,z196,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z611,z6]),(0,[z612,z0,z1,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z33,z5,z6]),(0,[z0,z19,z3,z4,z117,z5,z6]),(0,[z0,z1,z3,z4,z6,z154,z12]),(1,[z0,z1,z128,z117,z5,z6])],[(0,[z0,z1,z4,z8,z5,z6,z14]),(1,[z0,z57,z1,z3,z5,z6]),(1,[z0,z19,z3,z17,z4,z6]),(0,[z0,z1,z4,z5,z45,z6,z14]),(0,[z0,z555,z3,z4,z33,z5,z6]),(0,[z0,z104,z1,z16,z4,z5,z6]),(0,[z0,z613,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z614,z6]),(0,[z0,z327,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z46,z6]),(0,[z0,z1,z3,z4,z5,z615,z6])],[(0,[z58,z183,z1,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z616,z5,z6]),(0,[z0,z3,z4,z33,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z609,z6]),(0,[z0,z120,z1,z3,z4,z5,z12]),(0,[z0,z1,z3,z4,z5,z6,z80])],[(0,[z0,z1,z279,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z6,z617]),(0,[z618,z0,z1,z3,z4,z5,z6]),(0,[z0,z288,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z431,z33,z5,z6])],[(1,[z0,z288,z3,z4,z5,z6]),(0,[z0,z495,z3,z4,z5,z23,z6]),(0,[z0,z1,z16,z4,z5,z231,z6])],[(0,[z31,z0,z1,z4,z22,z5,z6]),(0,[z0,z36,z1,z3,z4,z18,z6]),(0,[z0,z3,z4,z5,z70,z6,z80])]],
   [[(0,[z7,z0,z1,z3,z5,z13,z6]),(0,[z619,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z161,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z620,z6]),(0,[z282,z0,z1,z4,z5,z6,z14])],[(0,[z0,z1,z3,z4,z5,z6,z621]),(0,[z0,z19,z1,z3,z4,z33,z6]),(0,[z0,z1,z3,z4,z33,z5,z6])],[(0,[z55,z0,z137,z3,z4,z5,z6]),(0,[z0,z56,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z6,z12]),(0,[z0,z1,z4,z22,z5,z6,z14])],[(0,[z0,z49,z1,z4,z5,z6,z14]),(1,[z0,z1,z3,z5,z141,z6]),(0,[z0,z1,z3,z4,z622,z5,z6]),(0,[z0,z1,z3,z4,z5,z623,z6]),(0,[z0,z40,z3,z4,z5,z46,z6]),(0,[z0,z1,z209,z3,z4,z5,z6])],[(0,[z0,z1,z624,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z6,z99]),(0,[z625,z0,z1,z3,z4,z5,z6]),(0,[z0,z626,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z627,z4,z5,z6])],[(0,[z0,z1,z16,z4,z8,z5,z6]),(0,[z0,z1,z3,z4,z5,z628,z6]),(0,[z0,z1,z15,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z629])],[(0,[z0,z630,z1,z3,z4,z5,z6]),(0,[z0,z3,z21,z4,z127,z5,z6]),(0,[z631,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z632,z3,z4,z5,z6]),(0,[z0,z191,z3,z4,z5,z70,z6])],[(0,[z0,z1,z16,z4,z22,z5,z6]),(0,[z0,z1,z3,z4,z633,z5,z6])]],
   [[(0,[z0,z19,z100,z3,z4,z5,z6]),(0,[z0,z1,z634,z3,z4,z5,z6])],[(0,[z29,z0,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z5,z635,z6]),(0,[z0,z1,z3,z4,z5,z636,z6]),(0,[z0,z1,z3,z4,z5,z6,z99]),(0,[z0,z1,z594,z4,z127,z5,z6]),(0,[z54,z0,z19,z3,z4,z5,z6]),(0,[z0,z1,z590,z3,z4,z5,z6]),(0,[z637,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z638,z6]),(0,[z84,z1,z25,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z639,z5,z6]),(0,[z0,z640,z1,z3,z4,z5,z6]),(0,[z0,z19,z179,z3,z4,z5,z6]),(0,[z0,z548,z1,z16,z4,z5,z6]),(0,[z0,z641,z1,z3,z4,z5,z6])],[(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z127,z5,z6,z12]),(0,[z0,z11,z1,z3,z4,z5,z12]),(0,[z642,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z643,z5,z6])],[(1,[z0,z1,z3,z4,z278,z6]),(0,[z84,z0,z28,z1,z4,z5,z6]),(0,[z0,z1,z4,z540,z5,z20,z6]),(0,[z0,z1,z3,z4,z5,z141,z6]),(0,[z0,z644,z1,z3,z4,z5,z6]),(0,[z645,z0,z1,z3,z4,z5,z6])],[(0,[z52,z1,z3,z4,z8,z5,z6]),(1,[z0,z646,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z647,z1,z3,z4,z5,z6]),(0,[z0,z531,z1,z3,z4,z5,z6]),(0,[z0,z19,z167,z3,z4,z5,z6]),(1,[z0,z19,z16,z4,z5,z6]),(1,[z0,z3,z4,z256,z5,z6]),(0,[z0,z66,z1,z3,z4,z5,z6])],[(0,[z0,z43,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z173,z127,z5,z6]),(0,[z0,z19,z120,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z648,z6]),(0,[z0,z1,z649,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z14,z617])],[(0,[z0,z1,z3,z4,z5,z650,z6]),(0,[z0,z1,z3,z473,z4,z5,z6]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z652,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z173,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z59,z4,z5,z6]),(0,[z0,z1,z4,z5,z13,z6,z350])],[(1,[z0,z19,z3,z4,z20,z6]),(0,[z0,z1,z646,z3,z4,z5,z6]),(0,[z58,z0,z1,z3,z4,z535,z6]),(0,[z0,z104,z19,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z23,z6]),(0,[z0,z1,z16,z299,z4,z5,z6]),(0,[z0,z1,z3,z4,z406,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z6])],[(0,[z0,z1,z3,z4,z653,z5,z6]),(1,[z52,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z654])],[(0,[z31,z1,z3,z279,z4,z5,z6]),(0,[z31,z0,z43,z1,z4,z5,z6]),(0,[z655,z0,z1,z3,z4,z5,z6]),(0,[z0,z100,z1,z3,z4,z20,z6]),(0,[z0,z1,z73,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z656,z6]),(0,[z0,z104,z1,z3,z4,z5,z6]),(0,[z0,z495,z1,z3,z4,z5,z6]),(0,[z0,z657,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z658,z4,z5,z6])],[(0,[z95,z0,z1,z16,z4,z5,z6]),(0,[z0,z19,z128,z3,z4,z5,z6]),(0,[z0,z1,z3,z18,z5,z46,z6]),(1,[z1,z3,z4,z5,z6,z232])],[(0,[z58,z0,z552,z3,z4,z5,z6]),(0,[z0,z167,z1,z3,z21,z5,z6]),(0,[z0,z1,z3,z659,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z660,z6]),(0,[z0,z1,z4,z5,z46,z6,z14]),(0,[z0,z3,z4,z5,z331,z46,z6])],[(0,[z284,z0,z1,z3,z4,z5,z20]),(0,[z0,z1,z181,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z32,z6,z99]),(0,[z0,z1,z3,z661,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z6]),(1,[z0,z1,z3,z567,z5,z6]),(0,[z0,z1,z3,z662,z4,z5,z6])],[(0,[z0,z1,z3,z4,z663,z5,z6]),(0,[z1,z3,z26,z4,z8,z5,z6]),(0,[z0,z664,z19,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z6,z140])]],
   [[(0,[z29,z0,z1,z3,z4,z278,z6]),(0,[z0,z1,z3,z4,z665,z5,z6]),(0,[z95,z0,z1,z3,z4,z20,z6]),(0,[z0,z1,z3,z4,z5,z394,z6]),(0,[z0,z100,z1,z3,z4,z131,z6]),(0,[z0,z100,z1,z3,z4,z70,z6]),(0,[z0,z1,z16,z4,z5,z13,z6]),(0,[z0,z429,z1,z3,z4,z5,z6])],[(0,[z0,z664,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z7,z52,z1,z3,z4,z5,z6]),(0,[z0,z666,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z250,z6])],[(0,[z7,z0,z1,z3,z21,z5,z6]),(1,[z0,z1,z3,z59,z5,z6]),(0,[z0,z1,z4,z5,z6,z654,z14])],[(0,[z0,z1,z667,z3,z4,z5,z6]),(0,[z29,z0,z1,z16,z4,z5,z6]),(0,[z84,z0,z1,z25,z4,z5,z6]),(0,[z52,z0,z19,z3,z4,z5,z6]),(0,[z0,z3,z21,z4,z33,z5,z6]),(0,[z0,z1,z16,z4,z5,z6,z27])],[(0,[z0,z1,z3,z508,z4,z5,z6]),(0,[z52,z0,z1,z3,z127,z5,z6]),(0,[z0,z149,z3,z4,z5,z20,z6]),(0,[z78,z0,z1,z3,z18,z5,z6]),(0,[z0,z1,z16,z17,z4,z5,z6])],[(0,[z52,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z668,z4,z5,z6]),(1,[z0,z1,z3,z396,z5,z6]),(0,[z669,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z50,z6]),(0,[z0,z1,z3,z4,z5,z670,z6]),(0,[z58,z1,z3,z26,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z671,z6]),(0,[z672,z0,z19,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z673,z6])],[(0,[z674,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z137,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z675,z6]),(0,[z0,z1,z3,z4,z567,z5,z6])]],
   [[(0,[z672,z0,z1,z3,z4,z5,z6]),(0,[z0,z19,z69,z3,z4,z5,z6]),(0,[z0,z3,z4,z117,z33,z5,z6]),(0,[z0,z1,z161,z4,z22,z5,z6])],[(0,[z676,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z677,z6]),(0,[z0,z1,z16,z4,z5,z32,z6]),(0,[z74,z0,z1,z3,z4,z5,z140])],[(1,[z0,z1,z3,z267,z5,z6]),(0,[z678,z0,z1,z3,z4,z5,z6]),(0,[z84,z0,z19,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z679]),(0,[z0,z1,z3,z4,z5,z680,z6]),(0,[z681,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z682,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z683]),(0,[z0,z1,z3,z4,z5,z6,z684])],[(0,[z0,z1,z685,z3,z4,z5,z6]),(1,[z0,z19,z36,z3,z4,z6]),(0,[z0,z1,z79,z4,z5,z6,z14])],[(0,[z0,z1,z3,z686,z4,z5,z6]),(0,[z687,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z688]),(1,[z0,z1,z594,z4,z5,z6]),(0,[z0,z689,z1,z3,z4,z5,z6]),(0,[z54,z0,z3,z4,z33,z5,z6]),(0,[z78,z0,z1,z4,z5,z6,z14]),(0,[z0,z1,z161,z3,z4,z22,z6]),(0,[z0,z1,z690,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z175])],[(0,[z0,z19,z3,z279,z4,z5,z6]),(0,[z0,z28,z1,z3,z4,z5,z6]),(0,[z691,z0,z1,z3,z4,z5,z6]),(1,[z0,z19,z3,z4,z5,z6]),(0,[z190,z0,z1,z4,z5,z6,z14]),(0,[z0,z188,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z105,z5,z70])],[(0,[z0,z66,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z4,z396,z5,z6]),(1,[z0,z155,z1,z4,z5,z14])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z693,z4,z5,z6]),(0,[z694,z0,z1,z3,z4,z5,z6]),(1,[z74,z0,z1,z3,z4,z140])]],
   [[(0,[z0,z1,z3,z4,z5,z695,z6]),(0,[z0,z69,z3,z73,z4,z5,z6]),(0,[z0,z28,z1,z69,z4,z5,z6]),(0,[z651,z0,z3,z4,z33,z5,z6]),(0,[z0,z36,z1,z3,z5,z46,z6]),(0,[z0,z1,z3,z696,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z175])],[(0,[z0,z1,z697,z3,z4,z5,z6]),(0,[z52,z1,z3,z4,z5,z32,z6]),(0,[z0,z120,z1,z4,z5,z6,z14])],[(0,[z29,z0,z1,z3,z4,z50,z6]),(0,[z95,z0,z19,z3,z4,z5,z6]),(0,[z58,z0,z646,z3,z4,z5,z6]),(0,[z0,z19,z3,z21,z4,z5,z6]),(0,[z0,z36,z1,z128,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z698]),(0,[z0,z1,z3,z4,z267,z5,z6]),(0,[z699,z0,z1,z3,z4,z5,z6]),(1,[z96,z1,z3,z4,z131,z6]),(0,[z0,z1,z3,z4,z97,z5,z6]),(0,[z0,z1,z3,z4,z5,z700,z6]),(0,[z0,z104,z1,z3,z4,z22,z6]),(1,[z0,z3,z4,z5,z485,z6]),(1,[z0,z1,z199,z4,z5,z6])],[(0,[z0,z1,z3,z279,z4,z5,z6]),(0,[z0,z1,z3,z701,z4,z5,z6]),(0,[z0,z702,z1,z3,z4,z5,z6]),(0,[z95,z0,z1,z3,z4,z5,z6]),(0,[z58,z0,z1,z16,z4,z5,z6]),(0,[z0,z703,z1,z3,z4,z5,z6]),(0,[z0,z210,z1,z4,z5,z6,z14]),(0,[z0,z104,z3,z4,z33,z5,z6]),(0,[z0,z1,z3,z76,z4,z5,z6])],[(0,[z0,z1,z3,z214,z4,z5,z6])],[(0,[z0,z1,z3,z704,z4,z5,z6]),(0,[z0,z19,z450,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z705,z6]),(0,[z0,z1,z3,z4,z706,z5,z6]),(0,[z0,z1,z479,z4,z5,z13,z6])],[(0,[z0,z1,z3,z4,z127,z5,z6]),(1,[z0,z1,z338,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z19,z3,z4,z268,z6]),(0,[z1,z3,z707,z8,z5,z6]),(0,[z0,z1,z4,z5,z6,z708])],[(0,[z0,z1,z3,z4,z5,z709]),(0,[z0,z19,z3,z710,z5,z6])],[(0,[z0,z149,z3,z4,z5,z6]),(0,[z0,z1,z711,z4,z5,z6]),(0,[z0,z35,z73,z4,z5,z6]),(0,[z0,z19,z3,z4,z6,z283]),(0,[z0,z104,z1,z4,z231,z6])],[(0,[z0,z1,z3,z4,z278,z6]),(0,[z0,z712,z1,z4,z5,z6]),(0,[z0,z167,z594,z127,z5,z6]),(0,[z78,z0,z1,z713,z5,z6])],[(0,[z95,z1,z3,z4,z714,z6]),(0,[z159,z1,z3,z4,z131,z6]),(0,[z0,z19,z16,z4,z5,z6]),(0,[z0,z1,z4,z5,z715,z6])],[(0,[z0,z716,z3,z4,z5,z6]),(0,[z0,z717,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z718,z6]),(0,[z0,z167,z3,z127,z5,z6]),(0,[z0,z3,z434,z127,z5,z6]),(0,[z3,z4,z33,z5,z6,z232])],[(1,[z0,z3,z4,z5,z719]),(0,[z720,z1,z3,z4,z5,z6]),(0,[z0,z1,z77,z76,z5,z6])],[(0,[z0,z66,z1,z5,z14,z27])],[(0,[z0,z1,z3,z721,z5,z6]),(0,[z0,z1,z4,z5,z228,z14]),(0,[z7,z1,z26,z5,z6,z14]),(0,[z0,z19,z4,z5,z152,z14]),(0,[z0,z19,z3,z4,z6,z304]),(0,[z0,z19,z3,z76,z70,z6]),(0,[z0,z1,z722,z4,z5,z6]),(0,[z0,z3,z567,z33,z5,z6]),(0,[z1,z3,z4,z5,z6,z723])],[(0,[z0,z149,z3,z4,z5,z394]),(0,[z0,z1,z724,z4,z5,z6]),(0,[z0,z1,z3,z725,z5,z6])],[(0,[z0,z726,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z232]),(0,[z0,z19,z3,z567,z5,z6])],[(0,[z0,z1,z727,z4,z5,z6]),(0,[z82,z0,z3,z4,z5,z152]),(0,[z0,z1,z3,z4,z5,z708])],[(0,[z0,z1,z3,z4,z5,z728]),(0,[z0,z1,z161,z4,z729,z6])],[(0,[z0,z1,z4,z278,z6,z14]),(0,[z0,z730,z3,z4,z5,z6]),(0,[z0,z1,z731,z4,z5,z6]),(0,[z0,z134,z1,z355,z4,z6])],[(0,[z0,z19,z3,z59,z5,z6]),(0,[z0,z265,z4,z5,z6,z14]),(0,[z0,z1,z16,z17,z18,z6]),(0,[z0,z1,z3,z5,z410,z27])]],
   [[(0,[z0,z1,z732,z4,z5,z6]),(0,[z0,z3,z4,z733,z5,z6]),(0,[z0,z734,z3,z4,z5,z6]),(0,[z0,z1,z735,z16,z5,z6])],[(0,[z95,z19,z3,z4,z20,z6]),(0,[z0,z646,z3,z4,z162,z6]),(0,[z0,z736,z3,z4,z5,z6])],[(0,[z0,z1,z737,z4,z5,z6]),(0,[z7,z1,z3,z707,z5,z6]),(0,[z0,z19,z3,z396,z5,z6]),(0,[z282,z1,z4,z5,z6,z654])],[(0,[z0,z1,z738,z4,z5,z6])],[(0,[z0,z72,z4,z33,z5,z6])],[(0,[z0,z3,z4,z33,z616,z6])],[(0,[z0,z739,z1,z3,z4,z5]),(0,[z0,z1,z16,z4,z5,z695])],[(0,[z0,z1,z3,z4,z740,z6]),(0,[z7,z1,z3,z5,z48,z6]),(0,[z0,z3,z59,z33,z5,z6]),(0,[z0,z19,z36,z3,z46,z6])],[(0,[z0,z19,z16,z4,z5,z101]),(0,[z0,z1,z3,z741,z5,z6])],[(0,[z0,z1,z3,z267,z5,z6]),(0,[z0,z1,z3,z97,z5,z6]),(0,[z0,z742,z3,z4,z5,z6])],[(0,[z0,z19,z36,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z743])],[(0,[z0,z19,z3,z316,z4,z6]),(0,[z0,z3,z4,z5,z6,z175]),(0,[z0,z1,z744,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z684])],[(0,[z0,z3,z4,z33,z278,z6]),(0,[z0,z745,z3,z4,z5,z6]),(0,[z0,z1,z417,z540,z5,z6]),(0,[z0,z1,z79,z5,z620,z6]),(0,[z0,z87,z16,z4,z5,z6]),(0,[z0,z191,z4,z5,z6,z14]),(0,[z0,z746,z3,z4,z5,z6])],[(0,[z0,z747,z3,z4,z5,z6]),(0,[z0,z1,z3,z707,z5,z6])],[(0,[z0,z1,z4,z5,z6,z748]),(0,[z0,z57,z3,z33,z5,z6]),(0,[z0,z28,z114,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z749]),(0,[z74,z0,z1,z3,z4,z140])],[(0,[z651,z137,z3,z4,z5,z6]),(1,[z1,z3,z4,z714,z6]),(0,[z74,z183,z0,z19,z3,z4]),(0,[z0,z19,z16,z4,z231,z6])]],
   [[(0,[z1,z3,z26,z5,z6,z192])],[(0,[z452,z3,z4,z403,z5,z6]),(0,[z0,z4,z33,z5,z6,z350]),(0,[z0,z1,z4,z455,z6,z578])],[(0,[z0,z750,z1,z3,z4,z5]),(0,[z0,z1,z199,z4,z5,z6]),(0,[z0,z495,z3,z325,z5,z6])],[(0,[z0,z19,z3,z4,z362,z6])],[(0,[z55,z137,z4,z5,z6,z14]),(0,[z0,z751,z1,z4,z5,z6]),(0,[z0,z19,z16,z4,z33,z6]),(0,[z0,z3,z173,z33,z5,z13])],[(0,[z0,z1,z752,z4,z5,z6]),(0,[z0,z252,z1,z3,z5,z27]),(0,[z0,z3,z33,z5,z6,z753]),(0,[z0,z1,z4,z6,z14,z754]),(0,[z0,z1,z16,z4,z755,z6])],[(0,[z0,z1,z756,z4,z5,z6]),(0,[z0,z1,z417,z5,z6,z14]),(0,[z0,z19,z3,z254,z4,z6]),(0,[z0,z19,z3,z4,z537,z6])],[(0,[z0,z757,z3,z4,z5,z6]),(0,[z0,z277,z3,z4,z5,z6]),(0,[z0,z356,z19,z4,z6,z14])],[(1,[z0,z1,z3,z758,z6])],[(0,[z0,z19,z3,z4,z162,z6]),(0,[z0,z19,z3,z4,z506,z6]),(0,[z0,z19,z4,z5,z330,z14]),(0,[z0,z1,z3,z173,z5,z759])],[(0,[z0,z19,z3,z760,z5,z6]),(0,[z0,z1,z3,z761,z5,z6]),(0,[z0,z36,z40,z3,z46,z6])],[(0,[z0,z1,z3,z4,z762,z6]),(0,[z280,z1,z3,z5,z32,z6])],[(0,[z0,z19,z763,z4,z5,z6]),(0,[z0,z1,z3,z4,z758,z6])],[(0,[z1,z764,z279,z4,z5,z6]),(0,[z0,z765,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z386,z6]),(0,[z0,z264,z1,z4,z6,z14])],[(0,[z0,z56,z1,z4,z5,z6]),(0,[z0,z1,z3,z766,z5,z6]),(0,[z0,z19,z3,z4,z403,z6])],[(0,[z29,z767,z3,z4,z5,z6]),(0,[z0,z4,z229,z540,z5,z6]),(0,[z0,z4,z33,z5,z6,z768])]],
   [[(0,[z0,z19,z702,z3,z4,z6]),(0,[z0,z4,z33,z5,z6,z123]),(0,[z0,z1,z222,z4,z5,z6])],[(0,[z0,z769,z3,z4,z5,z6]),(0,[z7,z0,z19,z36,z3,z6]),(0,[z284,z0,z57,z1,z3,z5]),(0,[z0,z36,z1,z46,z6,z14]),(0,[z0,z1,z4,z105,z70,z123])],[(0,[z0,z158,z1,z417,z5,z6]),(0,[z0,z3,z4,z5,z6,z770])],[(0,[z0,z1,z3,z4,z771,z6]),(0,[z0,z1,z3,z4,z772,z6]),(0,[z58,z280,z1,z3,z5,z6]),(0,[z0,z1,z4,z5,z366,z14])],[(0,[z0,z630,z3,z4,z33,z6]),(0,[z0,z181,z16,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z773]),(0,[z1,z3,z4,z5,z6,z774]),(0,[z775,z1,z3,z4,z5,z6]),(0,[z0,z77,z4,z33,z5,z6]),(0,[z0,z776,z3,z4,z5,z6]),(0,[z0,z429,z4,z5,z6,z14])],[(0,[z84,z25,z4,z33,z5,z6])],[(0,[z0,z1,z3,z4,z98,z6]),(0,[z0,z19,z3,z4,z105,z70])],[(0,[z0,z777,z3,z4,z5,z6])],[(0,[z0,z134,z1,z4,z6,z14]),(0,[z459,z0,z3,z372,z5,z6]),(0,[z0,z1,z4,z6,z154,z14])],[(0,[z0,z86,z4,z33,z5,z6])],[(0,[z0,z264,z49,z3,z4,z6]),(0,[z0,z19,z3,z4,z653,z6]),(0,[z0,z19,z4,z70,z6,z123]),(0,[z0,z100,z1,z3,z76,z6]),(0,[z404,z1,z3,z5,z13,z6])],[(0,[z0,z137,z3,z4,z50,z6]),(0,[z1,z3,z4,z5,z6,z778]),(0,[z0,z111,z16,z4,z5,z6])],[(0,[z0,z1,z16,z59,z5,z6]),(0,[z0,z120,z3,z4,z5,z121])],[(0,[z0,z4,z5,z6,z779,z14])],[(0,[z95,z1,z16,z4,z20,z6])],[(0,[z0,z780,z1,z3,z4,z5]),(0,[z0,z552,z3,z4,z162,z6]),(0,[z404,z66,z1,z3,z5,z6])]],
   [[(0,[z0,z158,z4,z33,z5,z6]),(0,[z0,z1,z781,z4,z5,z6]),(0,[z0,z1,z3,z782,z5,z6]),(0,[z0,z69,z4,z5,z609,z6]),(0,[z0,z19,z3,z4,z438,z6]),(0,[z0,z4,z5,z6,z783,z14])],[(0,[z0,z1,z784,z4,z5,z6]),(0,[z0,z785,z1,z3,z5,z6]),(0,[z0,z1,z4,z162,z6,z14]),(0,[z0,z1,z3,z786,z5,z6]),(0,[z0,z4,z33,z5,z6,z14]),(0,[z0,z1,z787,z4,z5,z6]),(0,[z0,z1,z4,z22,z207,z6])],[(0,[z0,z19,z3,z4,z545,z6]),(0,[z0,z19,z317,z4,z5,z6]),(0,[z0,z1,z4,z105,z70,z14])],[(0,[z0,z167,z3,z98,z127,z6]),(0,[z0,z3,z4,z5,z788,z6])],[(0,[z0,z1,z789,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z660])],[(0,[z0,z280,z1,z16,z5,z6]),(0,[z0,z1,z790,z4,z5,z6]),(0,[z0,z4,z33,z5,z6,z147]),(0,[z0,z1,z16,z76,z5,z6])],[(0,[z0,z120,z3,z267,z5,z6]),(0,[z0,z3,z4,z33,z260,z6]),(0,[z0,z1,z214,z117,z5,z6]),(0,[z0,z791,z3,z4,z5,z6]),(0,[z1,z4,z5,z6,z14,z792])],[(0,[z449,z1,z3,z4,z131,z6]),(0,[z0,z1,z4,z5,z6,z793])],[(0,[z7,z0,z134,z1,z3,z6])],[(0,[z31,z337,z1,z4,z5,z6]),(0,[z0,z36,z3,z331,z46,z6])],[(0,[z0,z3,z794,z4,z5,z6]),(0,[z0,z100,z3,z4,z229,z6]),(0,[z0,z1,z795,z4,z5,z6]),(0,[z0,z1,z713,z4,z5,z6]),(0,[z0,z36,z1,z16,z46,z6]),(0,[z74,z0,z429,z3,z4,z140])],[(0,[z0,z19,z4,z70,z6,z14]),(0,[z0,z1,z214,z5,z6,z136]),(0,[z0,z1,z3,z5,z6,z180])],[(0,[z0,z796,z1,z3,z5,z6]),(0,[z0,z1,z797,z4,z5,z6]),(0,[z0,z356,z19,z3,z4,z6]),(0,[z0,z19,z198,z3,z4,z6])],[(0,[z0,z1,z16,z4,z5,z504]),(0,[z0,z744,z4,z33,z5,z6])],[(0,[z0,z1,z3,z4,z5,z798]),(0,[z0,z1,z433,z4,z5,z14]),(0,[z0,z191,z3,z4,z5,z6]),(0,[z0,z1,z15,z251,z5,z6])],[(0,[z0,z3,z4,z5,z6,z799]),(0,[z58,z552,z3,z4,z5,z99])]],
   [[(0,[z0,z1,z4,z5,z6,z800]),(0,[z0,z1,z4,z5,z801,z6]),(0,[z0,z1,z339,z4,z535,z6]),(0,[z0,z19,z209,z4,z5,z6]),(0,[z0,z1,z128,z662,z5,z6])],[(0,[z0,z1,z802,z4,z5,z6]),(0,[z0,z1,z146,z4,z5,z6])],[(0,[z0,z264,z1,z3,z4,z6]),(0,[z0,z264,z3,z4,z121,z6])],[(0,[z0,z43,z299,z4,z5,z6])],[(0,[z0,z19,z3,z4,z638,z6]),(0,[z0,z1,z3,z803,z5,z6]),(0,[z0,z804,z3,z4,z5,z6]),(0,[z0,z805,z3,z4,z5,z6]),(0,[z0,z806,z1,z3,z4,z6]),(0,[z0,z167,z127,z5,z6,z14]),(0,[z0,z1,z807,z3,z4,z6])],[(0,[z0,z1,z808,z4,z5,z6])],[(0,[z0,z1,z3,z4,z809,z6]),(0,[z0,z1,z16,z4,z162,z6]),(0,[z0,z4,z33,z5,z810,z6]),(0,[z0,z161,z196,z4,z22,z6]),(0,[z0,z1,z4,z5,z6,z811])],[(0,[z0,z812,z3,z4,z5,z6]),(0,[z0,z1,z4,z813,z5,z394]),(0,[z0,z1,z814,z4,z5,z6]),(0,[z0,z815,z111,z3,z4,z6]),(0,[z0,z429,z3,z4,z70,z6])],[(0,[z0,z552,z317,z4,z5,z6]),(0,[z0,z19,z3,z4,z648,z6]),(0,[z0,z16,z4,z256,z5,z6])],[(0,[z0,z3,z4,z229,z5,z6]),(0,[z0,z1,z3,z816,z5,z6])],[(0,[z0,z411,z3,z4,z5,z12]),(0,[z58,z1,z3,z5,z141,z99])],[(0,[z1,z3,z4,z5,z774,z99]),(0,[z0,z19,z3,z4,z203,z6]),(0,[z0,z19,z3,z76,z5,z6]),(0,[z0,z40,z4,z5,z6,z14]),(0,[z0,z1,z817,z4,z5,z6])],[(0,[z0,z1,z3,z5,z6,z818]),(0,[z0,z19,z4,z33,z6,z14]),(0,[z0,z11,z16,z4,z5,z12]),(0,[z0,z1,z227,z4,z5,z6])],[(0,[z0,z819,z3,z4,z5,z6]),(0,[z0,z134,z1,z3,z4,z6]),(0,[z0,z820,z3,z4,z5,z6])],[(0,[z0,z1,z72,z4,z5,z6]),(0,[z0,z1,z4,z5,z628,z14])],[(0,[z0,z19,z454,z3,z4,z6])]],
   [[(0,[z0,z1,z821,z4,z5,z6]),(0,[z0,z1,z3,z822,z5,z6])],[(0,[z0,z1,z3,z417,z5,z6]),(0,[z0,z3,z4,z229,z5,z394]),(0,[z0,z1,z3,z59,z162,z6]),(0,[z0,z823,z3,z4,z5,z6])],[(0,[z284,z0,z19,z1,z3,z4]),(0,[z0,z158,z4,z229,z5,z6]),(0,[z0,z120,z3,z4,z5,z414])],[(0,[z0,z150,z179,z4,z5,z6]),(0,[z0,z1,z16,z4,z105,z70]),(0,[z0,z40,z3,z17,z4,z6])],[(0,[z0,z824,z3,z4,z5,z6]),(0,[z0,z825,z3,z4,z5,z6]),(0,[z58,z646,z3,z4,z5,z99])],[(0,[z0,z1,z3,z4,z5,z826]),(0,[z1,z3,z4,z5,z6,z827]),(0,[z0,z19,z4,z5,z6,z828]),(0,[z0,z100,z3,z4,z33,z6])],[(0,[z0,z302,z1,z4,z5,z14]),(0,[z0,z19,z3,z4,z526,z6]),(0,[z58,z1,z16,z4,z5,z99]),(0,[z0,z338,z4,z33,z5,z6]),(0,[z0,z1,z479,z173,z5,z13])],[(0,[z0,z689,z1,z3,z5,z27]),(0,[z0,z1,z4,z5,z6,z829])],[(0,[z0,z1,z3,z4,z830,z6]),(0,[z0,z19,z3,z4,z670,z6]),(0,[z0,z19,z3,z4,z671,z6]),(0,[z0,z36,z1,z199,z46,z6])],[(0,[z0,z1,z3,z417,z5,z394]),(0,[z0,z19,z86,z4,z5,z6])],[(0,[z0,z222,z4,z33,z5,z6]),(0,[z0,z11,z3,z396,z5,z12]),(0,[z0,z1,z79,z713,z5,z6]),(0,[z0,z1,z782,z5,z6,z14])],[(0,[z0,z1,z3,z4,z831,z6]),(0,[z0,z832,z3,z4,z5,z6]),(0,[z1,z3,z4,z714,z20,z6])],[(0,[z0,z833,z3,z4,z5,z6]),(0,[z358,z0,z19,z3,z4,z6]),(0,[z74,z0,z19,z4,z6,z14]),(1,[z0,z1,z3,z4,z834])],[(0,[z284,z0,z1,z3,z4,z5]),(0,[z0,z646,z317,z4,z5,z6]),(0,[z0,z28,z835,z4,z5,z6]),(0,[z0,z19,z3,z434,z4,z6]),(0,[z0,z1,z3,z4,z5,z719])],[(0,[z0,z1,z3,z836,z5,z6]),(0,[z0,z837,z1,z4,z5,z6])],[(0,[z0,z838,z1,z4,z5,z6]),(0,[z0,z839,z1,z3,z4,z5]),(0,[z0,z19,z3,z4,z45,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z840]),(0,[z0,z356,z1,z4,z23,z6]),(0,[z0,z1,z3,z758,z46,z6]),(0,[z0,z36,z40,z3,z4,z6]),(1,[z0,z815,z3,z4,z6])],[(0,[z29,z49,z3,z508,z5,z6]),(0,[z52,z1,z3,z395,z5,z6]),(0,[z284,z0,z19,z3,z4,z6]),(0,[z0,z3,z417,z33,z5,z6]),(0,[z58,z1,z3,z59,z5,z99])],[(0,[z0,z1,z3,z841,z5,z6]),(0,[z0,z36,z1,z3,z537,z6]),(0,[z0,z66,z111,z3,z5,z27])],[(0,[z0,z1,z3,z842,z5,z6]),(0,[z0,z1,z4,z5,z6,z247])],[(0,[z0,z1,z3,z4,z843,z6]),(0,[z0,z1,z844,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z845])],[(0,[z0,z1,z3,z846,z5,z6]),(0,[z0,z1,z847,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z848])],[(0,[z0,z1,z3,z4,z849,z6]),(0,[z1,z3,z4,z5,z32,z376]),(0,[z0,z1,z3,z4,z105,z257]),(0,[z0,z3,z4,z850,z5,z6]),(0,[z0,z1,z16,z4,z5,z53]),(0,[z0,z1,z3,z76,z105,z70])],[(0,[z0,z280,z1,z5,z6,z14]),(0,[z0,z1,z3,z851,z5,z6]),(0,[z0,z1,z4,z5,z133,z6]),(0,[z0,z1,z79,z5,z250,z6])],[(0,[z0,z852,z1,z4,z5,z6]),(0,[z0,z1,z853,z4,z5,z6])],[(0,[z0,z4,z33,z540,z5,z6]),(0,[z0,z1,z854,z4,z5,z6]),(0,[z0,z552,z4,z5,z6,z14]),(0,[z0,z1,z317,z59,z5,z6]),(0,[z0,z3,z4,z5,z719,z12])],[(0,[z855,z19,z3,z4,z5,z6]),(0,[z0,z196,z4,z5,z6,z14]),(0,[z0,z1,z16,z4,z856,z6]),(0,[z0,z191,z3,z5,z6,z180])],[(0,[z0,z1,z3,z857,z5,z6]),(0,[z284,z95,z1,z3,z4,z20]),(0,[z19,z450,z3,z4,z131,z6]),(0,[z58,z19,z3,z4,z5,z99])],[(0,[z55,z450,z3,z4,z5,z6]),(0,[z0,z1,z3,z325,z5,z6])],[(0,[z0,z1,z4,z5,z6,z858]),(0,[z0,z1,z4,z859,z5,z6]),(0,[z0,z1,z161,z4,z406,z6])],[(0,[z0,z56,z4,z33,z5,z6]),(0,[z1,z3,z707,z4,z5,z6]),(0,[z0,z149,z57,z3,z5,z6]),(0,[z860,z1,z4,z5,z6,z14])]],
   [[(0,[z0,z19,z666,z3,z4,z6]),(0,[z0,z288,z4,z5,z6,z14]),(0,[z0,z861,z3,z4,z5,z6])],[(0,[z0,z3,z4,z229,z278,z6]),(0,[z0,z210,z3,z862,z5,z6])],[(0,[z0,z210,z3,z21,z5,z6]),(0,[z0,z465,z3,z127,z5,z6]),(0,[z863,z1,z3,z4,z5,z6])],[(0,[z0,z1,z339,z4,z5,z6]),(0,[z52,z1,z3,z97,z5,z6]),(0,[z0,z57,z3,z229,z5,z6])],[(0,[z0,z1,z3,z5,z13,z679]),(0,[z0,z113,z3,z4,z33,z6]),(0,[z0,z265,z3,z4,z5,z6]),(0,[z0,z19,z161,z4,z22,z6])],[(0,[z0,z1,z128,z524,z5,z6])],[(0,[z0,z1,z3,z508,z5,z6]),(0,[z1,z3,z4,z5,z714,z6]),(0,[z0,z1,z16,z4,z5,z342]),(0,[z0,z19,z264,z3,z4,z6]),(0,[z0,z16,z4,z5,z6,z80]),(0,[z0,z1,z864,z4,z5,z6])],[(0,[z55,z56,z137,z4,z5,z6]),(0,[z0,z347,z1,z4,z5,z6]),(0,[z52,z1,z3,z707,z5,z6]),(0,[z0,z1,z4,z5,z6,z865]),(0,[z0,z19,z3,z4,z70,z6]),(0,[z0,z19,z4,z5,z6,z350]),(0,[z0,z104,z1,z4,z575,z6]),(0,[z0,z111,z209,z4,z5,z6]),(0,[z0,z1,z3,z4,z834,z140])],[(0,[z0,z149,z3,z417,z5,z6]),(0,[z0,z1,z5,z6,z123,z180])],[(0,[z0,z19,z4,z540,z20,z6]),(0,[z0,z11,z3,z4,z154,z12]),(0,[z0,z104,z1,z325,z5,z6])],[(0,[z0,z1,z306,z4,z5,z14]),(0,[z0,z19,z866,z4,z5,z6]),(0,[z0,z867,z1,z4,z6,z14]),(0,[z0,z1,z4,z5,z579,z14])],[(0,[z0,z1,z3,z868,z5,z6]),(0,[z0,z869,z3,z4,z5,z6]),(0,[z58,z1,z3,z4,z162,z99]),(0,[z0,z1,z3,z5,z758,z6])],[(0,[z0,z870,z1,z3,z5,z6]),(0,[z0,z871,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z872,z6]),(0,[z66,z1,z3,z5,z232,z27])],[(0,[z0,z1,z97,z5,z6,z14]),(0,[z0,z3,z4,z5,z6,z873]),(0,[z0,z40,z3,z4,z5,z6]),(0,[z0,z19,z3,z874,z5,z6])],[(0,[z0,z1,z591,z4,z5,z14]),(0,[z0,z19,z36,z3,z173,z6]),(0,[z0,z1,z875,z4,z5,z6]),(0,[z0,z1,z4,z5,z592,z14])],[(0,[z0,z646,z4,z5,z6,z14]),(0,[z0,z19,z496,z3,z4,z6]),(0,[z0,z19,z3,z4,z876,z6]),(0,[z0,z877,z3,z4,z5,z6])]],
   [[(0,[z0,z19,z36,z16,z4,z6]),(0,[z0,z1,z878,z4,z5,z6]),(0,[z78,z0,z79,z33,z5,z6])],[(0,[z0,z1,z3,z879,z5,z6]),(0,[z1,z3,z4,z131,z714,z6]),(0,[z74,z0,z19,z3,z4,z6]),(0,[z0,z1,z325,z5,z6,z14]),(0,[z0,z1,z5,z880,z6,z14])],[(0,[z0,z1,z4,z50,z6,z14]),(0,[z0,z1,z4,z813,z5,z6]),(0,[z0,z3,z4,z5,z6,z719]),(0,[z0,z3,z4,z5,z6,z881])],[(0,[z0,z882,z3,z4,z5,z6]),(1,[z0,z19,z3,z76,z6]),(0,[z0,z883,z3,z33,z5,z6])],[(0,[z0,z1,z317,z4,z162,z6]),(0,[z74,z0,z1,z16,z4,z140]),(0,[z0,z1,z76,z5,z6,z123])],[(0,[z0,z1,z3,z4,z5,z884]),(0,[z0,z429,z3,z4,z20,z6]),(0,[z0,z188,z1,z5,z250,z6])],[(0,[z0,z19,z4,z5,z6,z123]),(0,[z0,z1,z3,z885,z5,z6]),(0,[z0,z111,z3,z173,z5,z6])],[(0,[z7,z3,z26,z33,z5,z6]),(0,[z0,z1,z396,z5,z6,z14]),(0,[z0,z3,z4,z886,z5,z6])],[(0,[z0,z19,z66,z3,z5,z27])],[(0,[z55,z137,z3,z4,z5,z6]),(0,[z0,z264,z137,z3,z4,z6])],[(0,[z0,z1,z3,z4,z887,z6]),(0,[z31,z1,z279,z4,z5,z6]),(0,[z0,z888,z3,z4,z5,z6]),(0,[z0,z889,z1,z4,z5,z6]),(0,[z0,z120,z3,z4,z5,z719])],[(0,[z0,z1,z16,z108,z5,z6])],[(0,[z0,z1,z3,z890,z5,z6]),(0,[z0,z1,z891,z4,z5,z6]),(0,[z0,z87,z161,z4,z22,z6]),(0,[z0,z1,z4,z5,z101,z708])],[(0,[z0,z1,z3,z4,z6,z892]),(0,[z0,z19,z4,z540,z5,z6]),(0,[z0,z893,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z603,z14]),(0,[z894,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z895,z6]),(0,[z0,z288,z3,z4,z20,z6]),(0,[z0,z69,z835,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z896])],[(0,[z0,z264,z11,z3,z4,z6])]],
   [[(0,[z0,z19,z36,z3,z6,z27]),(0,[z0,z1,z627,z4,z5,z14]),(0,[z0,z327,z4,z5,z6,z352])],[(0,[z0,z1,z897,z4,z5,z6]),(0,[z0,z1,z3,z898,z5,z6]),(0,[z0,z3,z17,z18,z33,z6]),(0,[z0,z1,z713,z117,z5,z6]),(0,[z0,z104,z4,z485,z23,z6])],[(0,[z0,z3,z4,z33,z706,z6]),(0,[z78,z0,z1,z421,z5,z6]),(0,[z0,z899,z1,z4,z6,z14]),(0,[z0,z1,z900,z4,z5,z6])],[(0,[z0,z901,z3,z4,z5,z6]),(0,[z0,z902,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z759])],[(0,[z404,z19,z3,z4,z5,z6]),(0,[z0,z1,z86,z396,z5,z6]),(0,[z0,z903,z3,z4,z5,z6]),(0,[z0,z66,z1,z16,z5,z27])],[(0,[z0,z1,z4,z5,z635,z14]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z0,z1,z76,z5,z6,z14])],[(0,[z52,z0,z19,z36,z3,z6]),(0,[z0,z19,z3,z4,z535,z6]),(0,[z0,z1,z3,z4,z5,z905])],[(0,[z0,z19,z4,z5,z6,z14]),(0,[z0,z36,z1,z133,z46,z6]),(0,[z0,z111,z3,z5,z6,z27]),(0,[z906,z0,z1,z3,z5,z6])],[],[(0,[z0,z1,z16,z4,z5,z427]),(0,[z0,z689,z3,z4,z5,z12]),(0,[z0,z429,z3,z4,z5,z6])],[(0,[z404,z1,z3,z26,z5,z6]),(0,[z0,z1,z907,z4,z5,z6]),(0,[z0,z1,z3,z4,z908,z6]),(0,[z0,z1,z3,z4,z6,z909]),(0,[z0,z210,z3,z490,z5,z6])],[(0,[z0,z1,z3,z4,z5,z910]),(0,[z0,z3,z4,z911,z20,z6]),(0,[z0,z1,z4,z5,z650,z14]),(0,[z912,z19,z3,z4,z5,z6]),(0,[z0,z19,z4,z5,z6,z147]),(0,[z300,z0,z264,z3,z4,z6]),(0,[z0,z1,z913,z4,z5,z6])],[(0,[z0,z19,z3,z4,z663,z6]),(0,[z0,z1,z16,z914,z5,z6]),(0,[z0,z1,z4,z915,z5,z6])],[],[(0,[z29,z49,z16,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z916])],[(0,[z0,z917,z1,z4,z5,z6]),(0,[z0,z867,z1,z3,z4,z6]),(0,[z0,z44,z3,z127,z5,z6]),(0,[z0,z19,z3,z17,z4,z6])]],
   [[],[(0,[z159,z49,z3,z4,z5,z6]),(0,[z860,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z98,z256,z6]),(0,[z0,z19,z918,z4,z5,z6]),(0,[z0,z19,z919,z4,z5,z6]),(0,[z0,z19,z3,z108,z5,z6]),(0,[z0,z104,z1,z4,z23,z6])],[(0,[z0,z288,z3,z4,z5,z6]),(0,[z0,z19,z4,z131,z6,z14]),(0,[z0,z100,z3,z4,z6,z80]),(0,[z0,z495,z3,z567,z5,z6]),(0,[z0,z1,z3,z173,z5,z13])],[(0,[z0,z19,z920,z4,z5,z6]),(0,[z0,z921,z1,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z922]),(0,[z0,z1,z4,z5,z394,z14]),(0,[z0,z3,z4,z33,z6,z154])],[],[(0,[z96,z288,z3,z4,z131,z6]),(1,[z0,z835,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z923])],[(0,[z0,z57,z1,z3,z5,z394])],[(0,[z0,z1,z3,z4,z714,z6]),(0,[z651,z3,z4,z419,z5,z6]),(0,[z0,z1,z128,z643,z5,z6])],[(0,[z0,z924,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z925])],[(0,[z0,z1,z3,z926,z5,z6]),(0,[z0,z19,z3,z4,z257,z6]),(0,[z0,z3,z434,z550,z5,z6]),(0,[z0,z1,z16,z4,z5,z464])],[],[(0,[z0,z1,z927,z4,z5,z6]),(0,[z0,z928,z1,z3,z4,z6]),(0,[z0,z552,z3,z4,z535,z6]),(0,[z0,z4,z5,z6,z14,z929]),(0,[z0,z815,z3,z4,z5,z6])],[(0,[z52,z0,z134,z1,z3,z6]),(0,[z0,z475,z69,z4,z5,z6]),(0,[z0,z1,z3,z4,z729,z6]),(0,[z0,z930,z1,z4,z5,z6])],[(0,[z0,z19,z56,z4,z5,z6]),(0,[z0,z1,z79,z391,z5,z6]),(0,[z0,z28,z179,z4,z5,z6]),(0,[z0,z320,z19,z3,z4,z6])],[(0,[z0,z3,z4,z911,z5,z6]),(0,[z78,z0,z19,z36,z3,z6]),(0,[z0,z87,z4,z5,z6,z14])]],
   [[(0,[z0,z1,z3,z931,z5,z6]),(0,[z0,z3,z4,z932,z5,z6]),(0,[z0,z4,z5,z6,z80,z123])],[(0,[z0,z158,z19,z4,z20,z6]),(0,[z0,z1,z339,z97,z5,z6]),(0,[z0,z1,z3,z933,z5,z6]),(0,[z0,z3,z4,z70,z6,z934]),(0,[z74,z0,z3,z4,z175,z140])],[(0,[z0,z3,z4,z935,z5,z6])],[(0,[z0,z936,z3,z4,z5,z6]),(0,[z937,z19,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z759])],[(0,[z0,z1,z938,z4,z5,z6]),(0,[z52,z19,z3,z8,z5,z6])],[(0,[z0,z939,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z20,z6]),(0,[z0,z186,z299,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z940])],[(0,[z84,z19,z25,z4,z5,z6]),(0,[z0,z1,z941,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z942]),(0,[z0,z1,z943,z4,z5,z6]),(0,[z0,z1,z5,z6,z14,z944])],[(0,[z0,z835,z73,z4,z5,z6]),(0,[z0,z899,z1,z3,z4,z6]),(0,[z0,z3,z325,z5,z485,z6])],[(0,[z0,z1,z3,z945,z5,z6]),(0,[z0,z1,z77,z4,z5,z6])],[(0,[z0,z104,z1,z4,z729,z6])],[(0,[z84,z1,z4,z5,z6,z654]),(0,[z0,z946,z3,z4,z5,z6]),(0,[z0,z19,z3,z76,z4,z6])],[(0,[z1,z25,z764,z4,z5,z6]),(0,[z0,z19,z3,z4,z88,z6]),(0,[z0,z1,z4,z5,z6,z947]),(0,[z0,z1,z948,z4,z5,z6])],[(0,[z0,z1,z949,z4,z5,z6])],[(0,[z273,z49,z3,z4,z5,z6])],[(0,[z0,z594,z4,z33,z5,z6]),(0,[z0,z1,z950,z4,z5,z6])],[(0,[z7,z1,z3,z574,z5,z6]),(0,[z0,z951,z1,z4,z5,z6]),(0,[z0,z1,z952,z4,z5,z6])]],
   [[(0,[z0,z19,z3,z4,z50,z6]),(0,[z0,z1,z355,z4,z5,z6]),(0,[z0,z19,z479,z4,z5,z6])],[(0,[z0,z953,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z954,z6]),(0,[z0,z646,z3,z4,z535,z6]),(0,[z0,z134,z1,z3,z173,z6]),(0,[z0,z3,z21,z862,z5,z6]),(0,[z0,z3,z4,z33,z248,z6]),(0,[z0,z19,z3,z4,z256,z6]),(0,[z0,z4,z5,z6,z80,z14]),(0,[z404,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z18,z6,z304]),(0,[z74,z0,z1,z146,z4,z140])],[(0,[z0,z134,z167,z3,z127,z6]),(0,[z0,z3,z4,z5,z955,z6])],[(0,[z0,z19,z3,z4,z125,z6]),(0,[z0,z1,z16,z4,z535,z6]),(0,[z0,z134,z1,z16,z4,z6]),(0,[z956,z1,z3,z4,z5,z6]),(0,[z0,z16,z4,z5,z331,z6])],[(0,[z0,z3,z4,z419,z50,z6]),(0,[z7,z1,z3,z26,z5,z6]),(0,[z0,z1,z4,z22,z6,z578]),(0,[z0,z40,z199,z4,z5,z6])],[(0,[z0,z1,z957,z4,z5,z6]),(0,[z0,z158,z19,z4,z5,z6]),(0,[z0,z3,z4,z958,z535,z6]),(0,[z0,z134,z120,z3,z4,z6])],[(0,[z0,z3,z417,z229,z5,z6]),(0,[z0,z19,z594,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z959])],[(0,[z0,z1,z960,z4,z5,z6]),(0,[z95,z1,z4,z540,z20,z6]),(0,[z0,z181,z4,z5,z6,z14]),(0,[z0,z167,z3,z443,z5,z6]),(0,[z0,z3,z4,z5,z6,z961]),(0,[z0,z16,z962,z4,z5,z6])],[(0,[z0,z347,z4,z33,z5,z6]),(0,[z0,z1,z963,z4,z5,z6]),(0,[z0,z1,z3,z173,z5,z493]),(0,[z159,z664,z3,z4,z5,z6]),(0,[z151,z0,z1,z421,z5,z6])],[(0,[z0,z19,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z596,z14]),(0,[z0,z1,z4,z5,z6,z964]),(0,[z0,z19,z280,z3,z5,z6]),(0,[z0,z3,z4,z98,z33,z6]),(0,[z1,z4,z5,z6,z14,z232]),(0,[z0,z965,z4,z5,z6,z14]),(0,[z966,z1,z3,z4,z5,z6]),(0,[z0,z265,z222,z4,z5,z6])],[(0,[z0,z3,z4,z5,z6,z934])],[(0,[z0,z967,z3,z4,z5,z6]),(0,[z0,z1,z3,z968,z5,z6]),(0,[z84,z1,z764,z4,z5,z6]),(0,[z0,z969,z3,z4,z5,z6])],[(0,[z0,z1,z3,z970,z5,z6]),(0,[z212,z1,z3,z4,z20,z6]),(0,[z0,z3,z17,z971,z4,z6]),(0,[z0,z3,z325,z33,z5,z6]),(0,[z0,z290,z1,z4,z5,z14]),(0,[z0,z199,z4,z5,z331,z6]),(0,[z0,z1,z173,z5,z13,z350])],[(0,[z52,z1,z8,z5,z6,z14]),(0,[z96,z19,z3,z4,z131,z6])],[(0,[z0,z1,z3,z59,z535,z6]),(0,[z0,z1,z3,z4,z6,z154]),(0,[z0,z111,z4,z5,z6,z14])],[(0,[z0,z1,z972,z4,z5,z6]),(1,[z0,z3,z862,z5,z6]),(0,[z0,z973,z1,z3,z4,z6])]],
   [[(0,[z0,z19,z3,z4,z168,z6]),(0,[z55,z347,z137,z4,z5,z6]),(0,[z0,z19,z3,z4,z172,z6]),(0,[z0,z1,z974,z4,z5,z6]),(0,[z0,z19,z17,z4,z6,z14]),(0,[z0,z1,z16,z4,z5,z14])],[(0,[z0,z19,z3,z4,z5,z394]),(0,[z0,z1,z3,z975,z5,z6]),(0,[z0,z19,z338,z4,z5,z6])],[(0,[z0,z16,z196,z4,z5,z6]),(1,[z0,z1,z3,z5,z759])],[(0,[z0,z1,z976,z4,z5,z6]),(0,[z284,z0,z1,z16,z4,z5]),(0,[z0,z977,z1,z3,z5,z6]),(0,[z0,z134,z1,z3,z6,z27])],[(0,[z0,z1,z978,z4,z5,z6]),(0,[z95,z158,z1,z4,z20,z6]),(0,[z0,z264,z3,z4,z127,z6]),(0,[z0,z1,z3,z17,z18,z6]),(0,[z0,z1,z3,z105,z70,z180])],[(0,[z0,z19,z3,z4,z911,z6]),(0,[z300,z0,z3,z4,z5,z62]),(0,[z0,z979,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z105,z700]),(0,[z0,z3,z4,z5,z980,z6])],[(0,[z0,z1,z981,z4,z5,z6]),(0,[z0,z19,z3,z668,z4,z6]),(0,[z58,z1,z317,z4,z5,z99]),(0,[z0,z120,z3,z4,z5,z330]),(0,[z74,z0,z3,z4,z33,z140]),(0,[z0,z1,z4,z729,z23,z6])],[(0,[z0,z1,z3,z4,z5,z774]),(0,[z0,z1,z355,z4,z98,z6]),(0,[z0,z19,z3,z4,z426,z6]),(0,[z0,z982,z3,z4,z5,z6])],[(0,[z0,z4,z5,z6,z14,z175])],[(0,[z0,z552,z3,z97,z5,z6])],[(0,[z0,z1,z16,z4,z278,z6]),(0,[z0,z1,z5,z141,z6,z14]),(0,[z983,z1,z3,z4,z5,z6])],[(0,[z7,z0,z111,z3,z5,z6]),(0,[z0,z77,z4,z5,z6,z80])],[(0,[z0,z19,z3,z70,z6,z180])],[(0,[z0,z1,z3,z4,z5,z984]),(0,[z0,z495,z16,z4,z5,z6])],[(0,[z0,z552,z3,z4,z5,z6]),(0,[z0,z19,z128,z117,z5,z6]),(0,[z0,z3,z4,z5,z6,z80])]],
   [[(0,[z0,z19,z3,z4,z419,z6]),(0,[z0,z19,z4,z45,z6,z14]),(0,[z0,z3,z76,z33,z5,z6]),(0,[z404,z36,z1,z3,z5,z6])],[(0,[z52,z1,z16,z8,z5,z6]),(0,[z0,z985,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z98,z6])],[(0,[z0,z57,z1,z3,z5,z6]),(0,[z0,z986,z3,z4,z535,z6])],[(0,[z0,z1,z3,z4,z987,z6]),(0,[z637,z1,z3,z4,z20,z6]),(0,[z0,z1,z16,z4,z5,z211]),(0,[z988,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z989,z6])],[(0,[z0,z19,z3,z4,z231,z6]),(0,[z0,z1,z16,z4,z5,z708])],[(0,[z0,z1,z3,z990,z5,z6]),(0,[z0,z1,z3,z991,z5,z6]),(0,[z0,z19,z16,z4,z131,z6]),(0,[z0,z19,z992,z4,z5,z6]),(0,[z0,z1,z77,z5,z6,z180])],[(0,[z0,z1,z3,z993,z5,z6]),(0,[z0,z994,z3,z4,z5,z6]),(0,[z0,z995,z1,z4,z6,z14])],[],[(0,[z0,z1,z3,z996,z5,z6]),(0,[z997,z0,z1,z4,z5,z6]),(0,[z0,z191,z77,z4,z5,z6])],[(0,[z0,z1,z998,z4,z5,z6]),(0,[z0,z19,z3,z4,z33,z6])],[(0,[z0,z1,z16,z4,z5,z621]),(0,[z0,z1,z3,z5,z141,z6]),(0,[z0,z1,z3,z4,z755,z6]),(0,[z0,z999,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z708]),(0,[z0,z1,z4,z5,z6,z1000])],[(0,[z0,z1,z267,z5,z6,z14]),(0,[z0,z280,z3,z33,z5,z6]),(0,[z0,z167,z355,z127,z5,z6]),(0,[z0,z1,z1001,z4,z5,z6])],[(0,[z0,z1,z173,z5,z13,z14])],[(0,[z0,z1,z16,z4,z50,z6]),(0,[z0,z264,z11,z3,z4,z12])],[(0,[z0,z1,z4,z5,z6,z1002]),(0,[z0,z1,z92,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1003]),(0,[z0,z1004,z3,z4,z5,z6])],[(0,[z0,z1005,z1,z4,z5,z6]),(0,[z0,z646,z3,z97,z5,z6]),(0,[z0,z161,z4,z33,z22,z6]),(0,[z0,z1006,z1,z4,z5,z6])]],
   [[(0,[z0,z19,z3,z4,z497,z6]),(0,[z0,z36,z3,z33,z46,z6]),(0,[z0,z1007,z3,z4,z5,z6]),(0,[z0,z3,z1008,z4,z5,z6])],[(0,[z0,z19,z3,z4,z278,z6]),(0,[z0,z1,z16,z267,z5,z6]),(0,[z0,z1,z3,z1009,z5,z6])],[(0,[z159,z19,z3,z4,z131,z6]),(0,[z0,z19,z3,z4,z343,z6]),(0,[z0,z3,z21,z5,z319,z6]),(0,[z0,z104,z4,z33,z23,z6]),(0,[z0,z1010,z3,z4,z5,z6])],[(0,[z0,z19,z3,z4,z285,z6])],[(0,[z0,z646,z3,z4,z5,z6]),(0,[z0,z3,z4,z256,z5,z6]),(0,[z74,z0,z19,z3,z4,z140]),(0,[z0,z1011,z4,z33,z5,z6]),(0,[z0,z11,z86,z4,z5,z12])],[(0,[z0,z19,z3,z4,z272,z6])],[(0,[z0,z1,z16,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1012]),(0,[z0,z1013,z3,z4,z5,z6])],[(0,[z0,z3,z597,z4,z33,z6]),(0,[z0,z1,z3,z5,z1014,z6]),(0,[z74,z0,z19,z16,z4,z6]),(0,[z0,z36,z1,z3,z443,z6])],[(0,[z0,z3,z4,z958,z5,z6]),(0,[z0,z19,z3,z4,z301,z6])],[(0,[z0,z181,z3,z4,z5,z6]),(0,[z0,z11,z3,z108,z5,z12])],[(0,[z0,z1,z3,z4,z5,z1015])],[(0,[z0,z4,z33,z5,z6,z247]),(0,[z0,z1,z4,z5,z152,z14]),(0,[z0,z555,z3,z5,z319,z6]),(0,[z0,z264,z1,z16,z4,z6]),(0,[z0,z1,z1016,z5,z6,z14]),(0,[z0,z965,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1017,z5,z6]),(0,[z0,z19,z146,z4,z5,z6]),(0,[z0,z3,z4,z5,z272,z12])],[(0,[z0,z1,z4,z5,z6,z1018]),(0,[z96,z181,z3,z4,z131,z6]),(0,[z0,z1,z3,z567,z5,z6])],[(0,[z0,z104,z1,z4,z268,z6]),(0,[z0,z28,z169,z4,z5,z6]),(0,[z0,z1019,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z394]),(0,[z0,z3,z4,z5,z1020,z6])],[(0,[z0,z1,z3,z4,z1021,z6]),(0,[z0,z1,z4,z5,z6,z1022]),(0,[z0,z1,z108,z5,z6,z14])]],
   [[(0,[z0,z111,z3,z4,z5,z6]),(0,[z0,z4,z33,z5,z133,z6]),(0,[z0,z104,z1,z325,z23,z6])],[(0,[z0,z1,z3,z59,z5,z6]),(0,[z0,z1,z4,z5,z571,z14]),(0,[z0,z19,z1,z3,z76,z6])],[(1,[z284,z0,z19,z3,z4]),(0,[z183,z1,z16,z4,z5,z32]),(0,[z1023,z1,z3,z4,z5,z6]),(0,[z0,z1,z16,z761,z5,z6])],[(0,[z95,z1,z3,z4,z20,z6]),(0,[z0,z19,z3,z4,z622,z6])],[(0,[z0,z1,z3,z396,z5,z6]),(0,[z0,z19,z16,z4,z406,z6]),(0,[z0,z1,z4,z22,z729,z6])],[(0,[z242,z1,z25,z4,z5,z6]),(0,[z0,z3,z4,z1024,z5,z6]),(0,[z0,z16,z4,z5,z1025,z6])],[(0,[z0,z1,z3,z4,z1026,z6]),(0,[z0,z1,z1027,z4,z5,z6]),(0,[z270,z0,z19,z3,z4,z6]),(0,[z0,z1,z3,z1028,z5,z6])],[(0,[z0,z19,z3,z267,z5,z6]),(0,[z0,z36,z1,z3,z88,z6]),(0,[z0,z1029,z3,z4,z5,z6]),(0,[z0,z19,z3,z97,z5,z6]),(0,[z0,z19,z227,z4,z5,z6]),(0,[z78,z0,z1,z5,z221,z6])],[(0,[z0,z1,z3,z1030,z5,z6]),(0,[z52,z252,z1,z3,z5,z6]),(0,[z284,z0,z100,z1,z3,z4]),(0,[z78,z0,z19,z79,z5,z6])],[(0,[z0,z92,z4,z33,z5,z6])],[(0,[z0,z1031,z3,z4,z5,z6]),(0,[z0,z1,z128,z251,z5,z6]),(0,[z0,z1,z325,z22,z5,z6])],[(0,[z0,z1,z1032,z4,z5,z6]),(0,[z0,z1033,z3,z4,z5,z6]),(0,[z0,z3,z97,z33,z5,z6]),(0,[z0,z995,z1,z3,z4,z6]),(0,[z1034,z1,z16,z4,z5,z6])],[(0,[z0,z158,z57,z1,z5,z6]),(0,[z0,z1,z338,z396,z5,z6]),(0,[z0,z120,z92,z4,z5,z121]),(0,[z0,z1,z4,z5,z14,z156])],[(0,[z31,z1,z129,z4,z5,z6]),(0,[z284,z0,z1,z3,z4,z162]),(0,[z0,z1,z16,z4,z5,z688]),(0,[z74,z0,z19,z3,z4,z152]),(0,[z0,z155,z1,z4,z5,z14])],[(0,[z58,z320,z1,z3,z4,z5]),(0,[z0,z1,z16,z4,z98,z6])],[(0,[z0,z1,z1035,z4,z5,z6]),(0,[z0,z3,z971,z4,z5,z6]),(0,[z0,z1,z4,z5,z1036,z6])]],
   [[(0,[z0,z19,z199,z4,z5,z6]),(0,[z0,z1,z3,z1037,z5,z6])],[(0,[z0,z1038,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z229,z6])],[(0,[z0,z16,z4,z33,z5,z14])],[(0,[z0,z134,z3,z21,z4,z6]),(0,[z0,z184,z3,z443,z5,z6])],[(0,[z0,z1,z1039,z4,z5,z6]),(0,[z0,z1,z1040,z4,z5,z6]),(0,[z0,z3,z4,z340,z5,z272]),(0,[z0,z120,z16,z4,z5,z121]),(0,[z0,z1,z3,z5,z759,z27])],[(0,[z0,z986,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z530,z6]),(0,[z0,z134,z3,z4,z6,z12]),(0,[z0,z3,z396,z33,z5,z6]),(0,[z0,z1,z3,z5,z6,z1041])],[(0,[z0,z3,z4,z1042,z162,z6]),(0,[z0,z104,z495,z4,z23,z6]),(0,[z0,z531,z4,z5,z6,z197])],[(0,[z0,z1043,z1,z4,z5,z6]),(0,[z404,z1,z3,z8,z5,z6]),(0,[z0,z1,z128,z296,z5,z6]),(0,[z0,z3,z1044,z33,z5,z6])],[(0,[z52,z3,z8,z33,z5,z6]),(0,[z0,z1,z590,z4,z406,z6])],[(0,[z0,z3,z4,z5,z1045,z6]),(0,[z0,z120,z4,z5,z121,z14]),(0,[z0,z1046,z3,z4,z5,z6])],[(0,[z0,z3,z4,z1047,z5,z6]),(0,[z0,z3,z33,z5,z6,z180]),(0,[z74,z0,z1,z4,z14,z140]),(0,[z0,z40,z4,z5,z133,z6])],[(0,[z0,z1,z3,z4,z162,z6]),(0,[z0,z1,z4,z5,z330,z14]),(1,[z0,z3,z4,z876,z6])],[(0,[z0,z1,z3,z4,z5,z1048]),(0,[z95,z3,z4,z33,z20,z6]),(0,[z0,z57,z100,z1,z3,z6]),(0,[z0,z1049,z3,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z38])],[(0,[z0,z149,z16,z4,z5,z6]),(0,[z0,z43,z365,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z193]),(0,[z74,z0,z19,z3,z4,z330]),(0,[z0,z120,z4,z5,z121,z147])],[(0,[z0,z19,z347,z4,z5,z6]),(0,[z0,z1050,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1051,z6]),(0,[z0,z19,z222,z4,z5,z6]),(0,[z0,z1,z763,z4,z5,z6]),(0,[z0,z1,z3,z1052,z5,z6])],[(0,[z0,z158,z149,z4,z5,z6]),(0,[z58,z280,z1,z3,z5,z99]),(0,[z0,z28,z69,z4,z5,z6])]],
   [[(0,[z0,z19,z3,z4,z394,z20]),(0,[z0,z1053,z3,z4,z5,z6]),(0,[z0,z43,z73,z4,z5,z6]),(0,[z0,z277,z3,z17,z18,z6])],[(0,[z0,z1054,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1055]),(0,[z0,z167,z16,z127,z5,z6]),(0,[z0,z155,z1,z4,z5,z708])],[(0,[z0,z19,z134,z3,z4,z6]),(0,[z0,z1,z1056,z4,z5,z6]),(0,[z775,z19,z3,z4,z5,z6]),(0,[z0,z943,z4,z33,z5,z6]),(0,[z720,z1,z16,z4,z5,z6]),(0,[z0,z807,z111,z3,z4,z6])],[(0,[z0,z43,z835,z4,z5,z6]),(0,[z0,z1,z1057,z4,z5,z6]),(0,[z0,z1,z4,z5,z729,z6]),(0,[z0,z1,z16,z5,z6,z180]),(0,[z0,z36,z1,z3,z758,z6])],[(0,[z52,z496,z1,z3,z5,z6]),(0,[z0,z87,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1058,z5,z6])],[(0,[z0,z1,z1059,z4,z5,z6]),(0,[z0,z1,z3,z5,z1060,z6])],[(0,[z0,z128,z117,z33,z5,z6]),(0,[z0,z1,z3,z5,z13,z759])],[(0,[z0,z1,z3,z1016,z5,z6]),(0,[z0,z1,z3,z4,z105,z70])],[(0,[z0,z1,z4,z535,z6,z14])],[(0,[z0,z1061,z3,z4,z5,z6]),(0,[z0,z1,z4,z22,z176,z6]),(0,[z95,z149,z3,z4,z20,z6]),(0,[z0,z1062,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1063])],[(0,[z300,z0,z19,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z1064]),(0,[z0,z66,z1,z3,z5,z759]),(0,[z0,z1,z3,z4,z6,z834])],[(0,[z767,z1,z3,z4,z5,z6]),(0,[z0,z120,z3,z4,z5,z440]),(0,[z0,z1,z1065,z4,z5,z6]),(0,[z74,z0,z1,z3,z4,z162]),(0,[z0,z19,z3,z971,z4,z6])],[(0,[z0,z1066,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1067]),(0,[z0,z3,z17,z256,z18,z6])],[(0,[z0,z1068,z3,z4,z5,z6])]],
   [[],[(0,[z0,z120,z3,z396,z5,z6])],[(0,[z0,z1,z3,z4,z1069,z6]),(0,[z0,z1,z3,z1070,z5,z6]),(0,[z0,z19,z57,z3,z20,z6]),(0,[z0,z3,z4,z1071,z5,z6])],[(0,[z0,z1072,z3,z4,z5,z6]),(0,[z0,z1,z86,z108,z5,z6])],[(0,[z0,z1,z3,z4,z1073,z6]),(0,[z0,z1,z3,z4,z5,z1074]),(0,[z0,z1,z16,z97,z5,z6]),(0,[z0,z3,z4,z33,z162,z6]),(0,[z74,z0,z19,z146,z4,z6]),(0,[z0,z1,z713,z128,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1075]),(0,[z0,z1,z4,z1076,z5,z6]),(0,[z0,z1077,z3,z4,z5,z6])],[(0,[z0,z3,z267,z33,z5,z6]),(0,[z0,z1,z3,z710,z5,z6]),(0,[z0,z1,z3,z5,z6,z753]),(0,[z0,z1078,z3,z4,z5,z6])],[(0,[z0,z1,z5,z1014,z6,z14]),(0,[z0,z746,z16,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1079]),(0,[z0,z1,z1080,z4,z5,z6])],[(1,[z767,z3,z4,z5,z6]),(0,[z0,z19,z3,z5,z6,z180])],[(0,[z0,z1081,z1,z4,z5,z6]),(0,[z0,z19,z36,z3,z443,z6]),(0,[z0,z1082,z3,z4,z5,z6])],[(0,[z0,z19,z3,z417,z20,z6]),(0,[z58,z1,z3,z4,z535,z99]),(0,[z0,z3,z196,z4,z5,z6]),(0,[z0,z227,z4,z33,z5,z6]),(0,[z74,z0,z1,z3,z4,z834])],[(0,[z58,z1,z3,z4,z5,z774]),(0,[z1,z4,z5,z6,z14,z778])],[(0,[z0,z3,z835,z4,z5,z6]),(0,[z0,z1083,z1,z3,z4,z6]),(0,[z0,z100,z16,z4,z33,z6])],[(0,[z0,z1,z4,z5,z1084,z6]),(0,[z0,z1085,z1,z4,z5,z6]),(0,[z0,z495,z4,z5,z6,z14])],[(0,[z0,z1,z3,z1086,z5,z6]),(0,[z0,z1,z3,z4,z6,z1087]),(0,[z0,z3,z4,z5,z1088,z6])]],
   [[(0,[z0,z1,z1089,z3,z5,z6]),(0,[z0,z1,z3,z4,z6,z1090]),(0,[z0,z1,z3,z4,z856,z6]),(0,[z0,z1,z4,z5,z708,z14]),(0,[z0,z1,z3,z17,z758,z6])],[(0,[z29,z49,z4,z5,z6,z14]),(0,[z0,z3,z4,z33,z105,z70]),(0,[z0,z66,z265,z3,z5,z27])],[(0,[z0,z1,z3,z4,z1091,z6]),(0,[z0,z1,z4,z5,z440,z14]),(0,[z190,z1,z279,z4,z5,z6]),(0,[z0,z3,z4,z5,z1092,z6]),(0,[z0,z1,z209,z4,z5,z6]),(0,[z0,z3,z4,z5,z1093,z6]),(0,[z0,z277,z16,z4,z5,z6]),(0,[z0,z1,z1094,z4,z5,z6])],[(0,[z284,z0,z19,z3,z4,z5]),(0,[z0,z1095,z1,z3,z5,z6])],[(0,[z0,z552,z339,z4,z5,z6]),(0,[z0,z1,z317,z4,z535,z6]),(0,[z404,z1,z3,z21,z5,z6]),(0,[z0,z960,z4,z33,z5,z6])],[],[(0,[z49,z767,z3,z4,z5,z6]),(0,[z0,z19,z57,z3,z5,z6]),(0,[z0,z1096,z3,z4,z5,z6])],[(0,[z284,z0,z1,z3,z417,z5]),(0,[z0,z429,z3,z4,z131,z6])],[(0,[z0,z1,z1097,z4,z5,z6]),(0,[z0,z1,z713,z3,z5,z6])],[(0,[z0,z210,z3,z372,z5,z6]),(0,[z0,z19,z3,z4,z494,z6]),(0,[z0,z548,z1,z4,z231,z6])],[(0,[z0,z66,z3,z33,z5,z27]),(0,[z0,z3,z108,z33,z5,z6])],[(0,[z0,z66,z1,z3,z5,z596])],[(0,[z0,z484,z3,z21,z5,z6]),(0,[z0,z1098,z3,z4,z5,z6]),(0,[z0,z19,z72,z4,z5,z6]),(0,[z0,z35,z4,z431,z5,z6])],[(0,[z0,z1,z3,z5,z6,z1099]),(0,[z0,z1,z16,z4,z5,z101]),(0,[z0,z1,z3,z76,z5,z6])],[(0,[z284,z0,z3,z4,z229,z5]),(0,[z0,z19,z3,z822,z5,z6]),(0,[z0,z264,z3,z4,z33,z6]),(0,[z1100,z1,z4,z5,z6,z14]),(0,[z0,z1,z1101,z3,z5,z6])],[(0,[z0,z1,z1102,z3,z5,z6]),(0,[z0,z19,z3,z417,z5,z6]),(0,[z0,z1,z3,z5,z6,z1103]),(0,[z0,z1,z835,z4,z5,z6]),(0,[z0,z11,z3,z4,z5,z152]),(0,[z1104,z1,z4,z5,z6,z14]),(0,[z1,z16,z4,z5,z6,z232]),(0,[z0,z1105,z3,z4,z5,z6])]],
   [[],[(0,[z52,z0,z111,z3,z5,z6]),(0,[z0,z3,z4,z5,z6,z1106]),(0,[z0,z805,z3,z4,z162,z6])],[(0,[z0,z368,z1,z4,z5,z14])],[(0,[z0,z1,z3,z1107,z5,z6]),(0,[z0,z1108,z3,z4,z5,z6]),(0,[z0,z1,z3,z1109,z5,z6])],[(0,[z0,z1,z1110,z4,z5,z6]),(0,[z0,z19,z3,z75,z4,z6])],[(0,[z0,z11,z3,z4,z5,z719]),(0,[z0,z1,z16,z325,z5,z6]),(0,[z0,z111,z222,z4,z5,z6])],[(0,[z0,z1,z1111,z4,z5,z6]),(0,[z190,z1,z4,z5,z6,z617]),(0,[z0,z3,z4,z5,z6,z1112])],[(0,[z0,z3,z127,z5,z6,z603]),(0,[z0,z1,z4,z5,z6,z828]),(0,[z0,z883,z1,z3,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1113]),(0,[z0,z57,z1,z16,z5,z6]),(0,[z0,z19,z36,z128,z3,z6])],[(0,[z58,z1,z3,z4,z5,z596]),(0,[z0,z646,z339,z4,z5,z6]),(0,[z0,z1,z3,z97,z162,z6]),(0,[z0,z134,z3,z4,z33,z6]),(0,[z0,z1,z1114,z4,z5,z6])],[(0,[z0,z3,z4,z5,z1115,z6]),(0,[z0,z210,z16,z21,z5,z6]),(0,[z0,z555,z19,z3,z4,z6]),(0,[z0,z19,z36,z3,z372,z6]),(0,[z0,z11,z4,z5,z12,z14]),(0,[z0,z1,z4,z5,z14,z378])],[(0,[z84,z1,z4,z439,z5,z6]),(0,[z0,z339,z4,z33,z5,z6]),(0,[z0,z28,z4,z5,z6,z197])],[(0,[z0,z1,z3,z1116,z5,z6]),(0,[z0,z454,z1,z128,z5,z6]),(0,[z404,z1,z3,z18,z5,z6]),(0,[z0,z1,z3,z4,z70,z834])],[(1,[z0,z1,z713,z5,z6]),(0,[z0,z1,z1117,z4,z5,z6])],[(0,[z31,z323,z1,z4,z5,z6]),(0,[z0,z1118,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z509,z14]),(0,[z0,z1,z1011,z4,z5,z6]),(0,[z0,z194,z4,z5,z609,z6]),(0,[z0,z155,z4,z33,z5,z14]),(0,[z0,z1,z3,z5,z6,z944])],[(0,[z0,z1,z3,z760,z5,z6]),(0,[z0,z355,z4,z33,z5,z6]),(0,[z0,z16,z4,z5,z6,z175]),(0,[z0,z3,z4,z1119,z5,z6])]],
   [[(0,[z0,z49,z3,z4,z50,z6]),(0,[z0,z1,z3,z4,z5,z1120]),(0,[z0,z1,z1121,z4,z5,z6]),(0,[z0,z1122,z3,z4,z5,z6])],[(0,[z0,z19,z4,z5,z6,z247]),(0,[z0,z1,z1123,z4,z5,z6])],[(0,[z0,z19,z4,z20,z6,z14]),(0,[z0,z334,z3,z4,z5,z330])],[(0,[z0,z815,z66,z3,z4,z6])],[(0,[z0,z1,z3,z1124,z5,z6]),(0,[z0,z1,z3,z1125,z5,z6]),(0,[z0,z3,z4,z33,z492,z6]),(0,[z0,z19,z3,z4,z6,z934]),(0,[z0,z19,z77,z4,z70,z6]),(0,[z0,z11,z3,z4,z5,z12]),(0,[z0,z1,z4,z5,z435,z14]),(0,[z404,z1,z4,z5,z6,z14])],[(0,[z0,z1,z3,z173,z5,z451]),(0,[z0,z19,z3,z4,z700,z6]),(0,[z0,z327,z73,z4,z5,z6]),(0,[z0,z1,z1126,z4,z5,z6]),(0,[z0,z1,z3,z4,z1127,z6]),(0,[z0,z1128,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1129,z6]),(0,[z0,z19,z4,z5,z133,z6]),(0,[z0,z19,z3,z4,z599,z6]),(0,[z0,z16,z4,z5,z485,z6]),(0,[z1,z4,z5,z6,z14,z827])],[(0,[z0,z1,z1130,z4,z5,z6]),(0,[z0,z19,z3,z4,z63,z6]),(0,[z0,z1131,z4,z5,z6,z14])],[(0,[z0,z1,z3,z5,z1132,z6]),(0,[z0,z1,z4,z5,z341,z14]),(0,[z0,z1,z3,z1133,z5,z6]),(0,[z669,z1,z3,z26,z5,z6]),(0,[z0,z1,z1134,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z792])],[(0,[z284,z0,z3,z4,z33,z5]),(0,[z58,z1,z3,z97,z5,z99]),(0,[z0,z1,z1135,z4,z5,z6]),(0,[z0,z1,z4,z6,z1087,z14]),(0,[z0,z191,z16,z4,z5,z6])],[(0,[z0,z3,z4,z5,z1136,z6]),(0,[z0,z1137,z3,z4,z5,z6]),(0,[z0,z252,z1,z4,z5,z14]),(0,[z0,z19,z3,z4,z576,z6])],[(0,[z0,z19,z3,z325,z5,z6]),(0,[z0,z19,z3,z4,z6,z578]),(0,[z0,z19,z3,z4,z579,z6]),(0,[z0,z66,z1,z209,z5,z27])],[(0,[z0,z11,z338,z4,z5,z12])],[(0,[z0,z19,z3,z4,z6,z587]),(0,[z855,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z121,z62]),(0,[z0,z3,z4,z33,z6,z517]),(0,[z74,z0,z1,z227,z4,z140])],[(0,[z95,z1,z3,z4,z394,z20]),(0,[z58,z1,z3,z4,z5,z99]),(0,[z0,z135,z3,z127,z5,z6]),(0,[z0,z3,z4,z6,z154,z80])],[(0,[z0,z3,z4,z5,z331,z6])]],
   [[(0,[z1,z3,z764,z4,z5,z6]),(0,[z0,z317,z4,z33,z5,z6])],[(0,[z55,z137,z16,z4,z5,z6]),(0,[z0,z19,z339,z4,z5,z6])],[(0,[z0,z1,z317,z97,z5,z6])],[(0,[z0,z3,z962,z4,z5,z6])],[(0,[z0,z19,z3,z508,z5,z6]),(0,[z0,z1,z1138,z4,z5,z6])],[(0,[z0,z43,z697,z4,z5,z6]),(0,[z0,z100,z4,z33,z6,z14])],[(0,[z0,z1139,z3,z4,z5,z6]),(0,[z0,z555,z134,z3,z4,z6]),(0,[z0,z1,z161,z4,z22,z6])],[(0,[z0,z1,z317,z4,z5,z6]),(0,[z0,z1,z1140,z4,z5,z6]),(0,[z0,z3,z4,z1141,z5,z6])],[(0,[z0,z1,z3,z5,z6,z1142]),(0,[z0,z1,z3,z862,z5,z6])],[(0,[z0,z1,z1143,z4,z5,z6]),(0,[z0,z1,z3,z1144,z5,z6]),(0,[z0,z1,z3,z4,z1145,z6]),(0,[z0,z19,z3,z4,z6,z80]),(0,[z0,z1,z4,z5,z6,z350])],[(0,[z0,z19,z424,z3,z4,z6])],[(0,[z0,z16,z4,z33,z5,z6]),(0,[z0,z1146,z3,z4,z5,z6])],[(0,[z0,z1,z16,z417,z5,z6]),(0,[z0,z1,z866,z4,z5,z6])],[(0,[z0,z3,z4,z1147,z5,z6]),(0,[z0,z992,z1,z4,z5,z6]),(0,[z0,z191,z3,z76,z5,z6])],[],[(0,[z0,z1148,z1,z3,z4,z6]),(1,[z1,z764,z4,z5,z6]),(0,[z0,z3,z4,z1149,z5,z6]),(0,[z7,z19,z3,z26,z5,z6]),(0,[z0,z1,z3,z874,z5,z6]),(0,[z0,z19,z3,z658,z4,z6]),(0,[z0,z3,z396,z5,z6,z12])]],
   [[(0,[z0,z1,z1150,z4,z5,z6]),(0,[z1100,z1,z3,z4,z5,z6]),(0,[z0,z1,z1151,z4,z5,z6])],[(0,[z31,z1,z764,z4,z5,z6]),(0,[z52,z1,z3,z5,z71,z6]),(0,[z95,z3,z4,z229,z20,z6]),(0,[z0,z1152,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z876,z6]),(0,[z0,z429,z16,z4,z5,z6]),(0,[z0,z36,z1,z3,z46,z6])],[(0,[z0,z1,z3,z1153,z4,z5]),(0,[z293,z450,z3,z4,z5,z6]),(0,[z1,z3,z4,z1154,z5,z6])],[(0,[z0,z585,z3,z4,z33,z6]),(0,[z0,z134,z1,z594,z4,z6]),(0,[z0,z523,z1,z4,z5,z14])],[(0,[z0,z1,z3,z4,z1155,z6]),(0,[z0,z1156,z3,z4,z5,z6]),(0,[z0,z19,z3,z885,z5,z6]),(0,[z0,z199,z4,z33,z5,z6]),(0,[z0,z1,z1157,z4,z5,z6]),(0,[z74,z0,z429,z3,z4,z6])],[(0,[z0,z1,z508,z5,z6,z14]),(0,[z7,z1,z3,z436,z5,z6])],[(0,[z84,z644,z1,z4,z5,z6]),(0,[z0,z264,z210,z3,z4,z6])],[(0,[z153,z137,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z1158,z6]),(0,[z58,z3,z4,z33,z5,z99]),(0,[z0,z104,z19,z4,z23,z6]),(0,[z0,z853,z4,z33,z5,z6]),(0,[z0,z1,z4,z5,z6,z768])],[(0,[z0,z1,z3,z1159,z5,z6]),(0,[z31,z19,z279,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z123]),(0,[z242,z1,z425,z4,z5,z6]),(0,[z0,z1,z1160,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1161]),(0,[z95,z1,z3,z417,z20,z6]),(0,[z19,z3,z4,z131,z20,z6]),(0,[z0,z19,z3,z4,z6,z154]),(0,[z0,z1,z1162,z4,z5,z6])],[(0,[z0,z1,z735,z3,z5,z6]),(0,[z284,z0,z1,z3,z4,z105]),(0,[z0,z1,z3,z4,z6,z1163]),(0,[z0,z19,z16,z4,z45,z6]),(0,[z0,z1,z4,z5,z6,z1164]),(0,[z0,z1165,z4,z5,z6,z14]),(0,[z0,z1,z16,z173,z5,z13])],[(0,[z0,z1,z3,z18,z125,z6]),(0,[z0,z57,z1,z5,z6,z14]),(0,[z0,z134,z167,z3,z4,z6]),(0,[z0,z3,z4,z5,z1166,z6])],[],[(0,[z0,z1,z3,z4,z105,z162])],[(0,[z0,z19,z3,z4,z176,z6]),(0,[z0,z1,z3,z4,z70,z683])],[(0,[z0,z16,z4,z33,z5,z101])]],
   [[(0,[z0,z19,z148,z3,z4,z6]),(0,[z0,z104,z1,z567,z23,z6])],[(0,[z0,z1167,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1168]),(0,[z0,z479,z4,z33,z5,z6]),(0,[z0,z1169,z3,z4,z5,z6])],[(0,[z0,z1,z16,z1101,z5,z6])],[(0,[z0,z19,z3,z4,z665,z6]),(0,[z0,z288,z3,z4,z131,z6]),(0,[z0,z1,z3,z1044,z5,z6]),(0,[z0,z4,z5,z331,z6,z14]),(0,[z0,z1,z5,z6,z14,z180])],[(0,[z0,z1,z1170,z4,z5,z6]),(0,[z0,z1,z3,z4,z1171,z6]),(0,[z0,z1,z1172,z4,z5,z6]),(0,[z0,z19,z3,z4,z5,z905]),(0,[z0,z742,z4,z5,z6,z14])],[(0,[z0,z177,z3,z127,z5,z6]),(0,[z284,z0,z1,z4,z5,z14]),(0,[z0,z43,z473,z4,z5,z6]),(0,[z0,z1,z199,z18,z5,z6])],[(0,[z767,z137,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1173,z6])],[(0,[z29,z3,z4,z403,z5,z6]),(0,[z0,z1,z4,z540,z5,z394])],[(0,[z0,z1,z3,z4,z535,z6]),(0,[z0,z1,z4,z5,z1174,z6]),(0,[z1175,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z18,z6,z14]),(0,[z1176,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z1177]),(0,[z0,z19,z3,z4,z458,z6]),(0,[z0,z1131,z3,z4,z5,z6])],[(0,[z0,z3,z4,z33,z876,z6])],[(0,[z29,z49,z3,z4,z278,z6]),(0,[z0,z3,z4,z5,z6,z929]),(0,[z0,z1178,z3,z4,z5,z6]),(0,[z0,z191,z3,z4,z105,z70]),(0,[z0,z1,z3,z4,z105,z834])],[(0,[z0,z158,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1179])],[(0,[z284,z0,z149,z3,z4,z5]),(0,[z0,z1,z4,z5,z6,z147]),(0,[z912,z1,z3,z4,z5,z6])],[(0,[z0,z1180,z1,z4,z5,z6]),(1,[z0,z19,z57,z3,z6]),(0,[z0,z1,z86,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1181,z6]),(0,[z0,z265,z16,z4,z5,z6]),(0,[z0,z1,z3,z18,z758,z6])]],
   [[(0,[z0,z3,z267,z5,z6,z12]),(0,[z0,z19,z3,z173,z5,z13])],[(0,[z0,z1,z16,z508,z5,z6]),(0,[z672,z0,z473,z4,z5,z6]),(0,[z0,z1182,z3,z4,z5,z6])],[(0,[z0,z19,z3,z701,z4,z6]),(0,[z0,z19,z16,z4,z70,z6]),(0,[z0,z1183,z3,z4,z5,z6])],[(0,[z0,z1,z3,z5,z1184,z6]),(0,[z0,z1,z3,z108,z5,z6]),(0,[z0,z1,z918,z4,z5,z6]),(0,[z0,z1,z919,z4,z5,z6]),(0,[z0,z146,z4,z33,z5,z6])],[(0,[z0,z1,z4,z1185,z5,z6]),(0,[z0,z158,z1,z4,z5,z394]),(0,[z0,z167,z3,z862,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1186]),(0,[z0,z1,z920,z4,z5,z6]),(0,[z0,z3,z1187,z4,z5,z6])],[(0,[z0,z1188,z1,z4,z5,z6]),(0,[z31,z279,z4,z33,z5,z6]),(0,[z0,z19,z564,z3,z4,z6]),(0,[z0,z3,z4,z1189,z5,z6]),(0,[z0,z1,z1190,z4,z5,z6]),(0,[z404,z66,z1,z3,z5,z27])],[(0,[z0,z19,z3,z4,z5,z925])],[(0,[z0,z1,z3,z4,z5,z1191]),(0,[z0,z1,z1192,z4,z5,z6]),(0,[z0,z1,z3,z17,z213,z6]),(0,[z0,z100,z3,z4,z876,z6]),(0,[z0,z40,z16,z4,z5,z6]),(0,[z0,z265,z209,z4,z5,z6])],[(0,[z0,z1193,z3,z4,z5,z6]),(0,[z284,z0,z19,z3,z4,z20]),(0,[z0,z1,z339,z59,z5,z6]),(0,[z0,z1,z4,z5,z1194,z6])],[(0,[z0,z1,z3,z5,z1195,z6]),(0,[z0,z1,z4,z5,z6,z1196]),(0,[z0,z1,z3,z1197,z5,z6]),(0,[z0,z1198,z3,z4,z5,z6])],[(0,[z0,z3,z4,z1199,z5,z6]),(0,[z0,z1,z338,z108,z5,z6]),(0,[z0,z1,z3,z5,z1200,z6])],[(0,[z0,z1,z3,z1201,z5,z6]),(0,[z0,z3,z4,z5,z6,z779]),(0,[z7,z1,z16,z26,z5,z6]),(0,[z0,z19,z36,z3,z17,z6])],[(0,[z29,z49,z3,z4,z50,z6]),(0,[z0,z1,z1202,z4,z5,z6]),(0,[z284,z0,z1,z998,z4,z5]),(0,[z0,z1,z1203,z4,z5,z6])],[(0,[z0,z1,z1204,z4,z5,z6]),(0,[z0,z1,z4,z5,z810,z6]),(0,[z74,z0,z19,z3,z4,z70]),(0,[z0,z1,z567,z5,z6,z14]),(0,[z0,z1205,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z834])],[(0,[z0,z1,z3,z4,z1206,z6]),(0,[z404,z3,z4,z33,z5,z6])]],
   [[(0,[z0,z1,z1207,z4,z5,z6]),(0,[z95,z1,z4,z20,z6,z14]),(0,[z0,z3,z1208,z4,z5,z6])],[(0,[z29,z49,z3,z267,z5,z6]),(0,[z0,z3,z4,z33,z535,z6]),(0,[z19,z3,z4,z5,z6,z232]),(0,[z0,z3,z4,z5,z1025,z6])],[(0,[z0,z1,z3,z4,z1209,z6]),(0,[z284,z0,z158,z1,z4,z5])],[(0,[z0,z1,z3,z5,z880,z6]),(0,[z0,z495,z3,z4,z5,z6]),(0,[z0,z969,z16,z4,z5,z6])],[(0,[z0,z1,z3,z1210,z5,z6]),(0,[z0,z1,z3,z914,z5,z6])],[(0,[z0,z19,z57,z3,z4,z6]),(0,[z937,z1,z3,z4,z5,z6]),(0,[z0,z36,z1,z3,z575,z6])],[(0,[z29,z49,z3,z4,z5,z6]),(0,[z52,z1,z3,z8,z5,z6]),(0,[z0,z149,z4,z540,z5,z6]),(0,[z0,z19,z77,z4,z5,z6]),(0,[z0,z1,z16,z4,z6,z154])],[(1,[z1,z3,z707,z5,z6]),(0,[z0,z19,z3,z4,z6,z311])],[(0,[z84,z1,z25,z4,z5,z6]),(0,[z58,z1,z4,z5,z99,z14]),(0,[z0,z191,z4,z5,z6,z123])],[],[(0,[z0,z19,z3,z4,z131,z6]),(0,[z0,z4,z256,z5,z6,z14])],[(0,[z96,z1,z3,z4,z714,z6]),(0,[z0,z1,z3,z18,z285,z6]),(0,[z0,z1,z16,z4,z5,z512]),(0,[z0,z3,z4,z105,z70,z80])],[(0,[z0,z1,z4,z5,z6,z1211]),(0,[z0,z1165,z3,z4,z5,z6]),(0,[z0,z1,z59,z5,z6,z14]),(0,[z0,z4,z5,z133,z331,z6])],[(0,[z284,z0,z1,z4,z540,z5]),(0,[z183,z1,z3,z4,z5,z373]),(0,[z1,z3,z4,z5,z6,z1212])],[(0,[z0,z3,z4,z1213,z5,z6]),(0,[z52,z641,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z1214,z6]),(0,[z0,z19,z355,z4,z5,z6])],[(0,[z0,z280,z1,z3,z5,z6])]],
   [[(0,[z0,z1,z4,z5,z6,z1215]),(0,[z0,z149,z4,z5,z6,z14]),(0,[z553,z0,z19,z3,z4,z6]),(0,[z0,z1216,z3,z4,z5,z6]),(0,[z0,z1,z4,z6,z14,z1163]),(0,[z216,z1,z129,z4,z5,z6]),(0,[z0,z815,z1,z3,z4,z6])],[(0,[z284,z0,z1,z972,z4,z5]),(0,[z0,z1,z3,z4,z1217,z6]),(0,[z956,z19,z3,z4,z5,z6]),(0,[z0,z356,z1,z4,z6,z122]),(0,[z0,z1,z4,z5,z6,z1218])],[(0,[z0,z1,z3,z4,z50,z6]),(0,[z0,z1,z479,z4,z5,z6]),(0,[z0,z1,z1219,z4,z5,z6]),(0,[z0,z1220,z3,z4,z5,z6])],[(0,[z0,z19,z3,z4,z430,z6]),(0,[z0,z1,z339,z4,z162,z6]),(0,[z0,z3,z4,z876,z45,z6])],[(0,[z0,z57,z1,z540,z5,z6]),(0,[z0,z3,z1221,z33,z5,z6]),(0,[z1104,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1222,z5,z6])],[(0,[z0,z3,z4,z1042,z5,z6]),(0,[z0,z1,z1223,z4,z5,z6]),(0,[z0,z1,z1224,z4,z5,z6])],[(0,[z0,z552,z16,z4,z5,z6])],[(0,[z0,z1,z594,z4,z5,z6]),(0,[z0,z19,z3,z659,z4,z6])],[(0,[z0,z1,z3,z4,z1225,z6]),(0,[z0,z1226,z3,z4,z5,z6]),(0,[z0,z3,z33,z5,z141,z6]),(0,[z1227,z1,z3,z4,z5,z6]),(0,[z0,z513,z3,z21,z5,z6])],[(0,[z0,z3,z4,z5,z6,z1228]),(0,[z0,z19,z3,z970,z5,z6]),(0,[z0,z19,z16,z17,z4,z6])],[(0,[z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z16,z4,z5,z387])],[(0,[z0,z288,z16,z4,z5,z6]),(0,[z0,z1,z3,z1229,z5,z6])],[(0,[z0,z1,z3,z4,z1230,z6]),(0,[z997,z0,z19,z4,z5,z6]),(0,[z0,z19,z3,z4,z398,z6]),(0,[z0,z19,z16,z4,z5,z14]),(0,[z0,z1,z4,z5,z6,z1231]),(0,[z0,z209,z4,z33,z5,z6])],[(0,[z96,z1,z3,z4,z131,z6]),(0,[z0,z3,z4,z5,z485,z6])]],
   [[(0,[z0,z3,z508,z33,z5,z6]),(0,[z0,z1232,z3,z4,z5,z6]),(0,[z0,z1,z4,z98,z6,z14]),(0,[z0,z475,z291,z4,z5,z6])],[],[(0,[z0,z767,z3,z4,z5,z6]),(0,[z0,z1,z4,z540,z5,z6]),(0,[z0,z552,z3,z59,z5,z6]),(0,[z0,z1,z16,z5,z141,z6]),(0,[z0,z19,z3,z17,z18,z6]),(0,[z0,z1,z3,z1221,z5,z6]),(0,[z0,z3,z4,z5,z6,z1233]),(0,[z0,z1,z77,z4,z105,z70])],[(0,[z0,z1,z3,z4,z5,z394]),(0,[z58,z1,z339,z4,z5,z99]),(0,[z0,z1,z338,z4,z5,z6])],[(0,[z404,z1,z3,z97,z5,z6]),(0,[z0,z19,z155,z4,z5,z14]),(0,[z0,z1,z1234,z4,z5,z6])],[(0,[z0,z1,z764,z4,z5,z6]),(0,[z0,z1235,z3,z4,z5,z6]),(0,[z0,z3,z862,z127,z5,z6]),(0,[z0,z3,z4,z5,z121,z719]),(0,[z0,z3,z4,z5,z6,z783]),(0,[z0,z1,z4,z5,z6,z1236])],[(0,[z0,z1,z3,z97,z535,z6]),(0,[z0,z3,z862,z4,z5,z6]),(0,[z0,z210,z21,z5,z6,z14]),(0,[z0,z4,z33,z5,z1084,z6])],[(0,[z95,z57,z1,z3,z20,z6]),(0,[z0,z3,z4,z5,z6,z1237])],[(0,[z404,z1,z3,z127,z5,z6]),(0,[z0,z4,z5,z6,z14,z961])],[(0,[z404,z1,z3,z4,z5,z6]),(0,[z0,z19,z3,z4,z406,z6])],[(0,[z0,z19,z4,z6,z578,z14]),(0,[z0,z1,z3,z4,z1238,z6]),(0,[z0,z1,z931,z5,z6,z14])],[(0,[z0,z3,z4,z33,z50,z6]),(0,[z0,z1,z1239,z4,z5,z6]),(0,[z0,z66,z1,z3,z5,z27]),(0,[z0,z3,z76,z5,z6,z80])],[(0,[z0,z646,z16,z4,z5,z6]),(0,[z0,z1,z16,z4,z5,z469])],[(0,[z0,z1,z1240,z4,z5,z6]),(0,[z0,z19,z90,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1241,z6]),(1,[z0,z1,z4,z729,z6])],[(0,[z58,z74,z0,z19,z3,z4]),(0,[z0,z1,z4,z5,z6,z1242]),(0,[z78,z0,z1,z79,z5,z6]),(0,[z0,z1,z3,z4,z6,z754])]],
   [[(0,[z0,z19,z16,z4,z20,z6]),(0,[z0,z16,z4,z229,z5,z6]),(0,[z0,z1,z594,z4,z98,z6]),(0,[z74,z0,z19,z227,z4,z6]),(0,[z1034,z1,z3,z4,z5,z6])],[(0,[z0,z1243,z1,z4,z5,z6]),(0,[z988,z19,z3,z4,z5,z6]),(0,[z0,z1,z128,z117,z5,z6])],[(0,[z0,z19,z533,z3,z4,z6])],[(0,[z1,z3,z26,z97,z5,z6])],[(0,[z0,z3,z4,z33,z5,z6]),(0,[z55,z767,z3,z4,z5,z6]),(0,[z0,z19,z57,z1,z3,z6]),(0,[z74,z0,z1,z3,z4,z152]),(0,[z0,z1,z4,z5,z195,z14]),(0,[z0,z3,z567,z5,z485,z6])],[(0,[z0,z19,z36,z4,z6,z14]),(0,[z0,z3,z4,z5,z876,z6]),(0,[z0,z1,z16,z567,z5,z6]),(0,[z0,z1244,z3,z4,z5,z6]),(0,[z0,z277,z4,z5,z6,z14]),(0,[z0,z66,z1,z222,z5,z27])],[(0,[z0,z1,z3,z1245,z5,z6]),(0,[z0,z4,z229,z5,z6,z14])],[(0,[z0,z1246,z1,z3,z4,z6]),(0,[z1,z3,z26,z707,z5,z6]),(0,[z0,z646,z3,z59,z5,z6]),(0,[z0,z1,z1247,z4,z5,z6]),(0,[z0,z1248,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1249,z6]),(0,[z0,z19,z3,z5,z141,z6]),(0,[z0,z1,z3,z173,z5,z386])],[(0,[z0,z1,z3,z4,z5,z1250]),(0,[z0,z1,z3,z1251,z5,z6]),(0,[z0,z1243,z1,z4,z5,z394]),(0,[z0,z4,z5,z485,z6,z14])],[(0,[z0,z100,z3,z4,z256,z6])],[(0,[z0,z1,z3,z1252,z5,z6]),(0,[z0,z1253,z1,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1254]),(0,[z0,z1,z1255,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z394]),(0,[z0,z19,z92,z4,z5,z6]),(0,[z0,z1,z16,z396,z5,z6]),(0,[z0,z36,z1,z199,z5,z6])],[(0,[z0,z19,z3,z4,z639,z6]),(0,[z0,z3,z5,z6,z80,z180])],[(0,[z284,z0,z1,z3,z4,z140])],[(0,[z0,z3,z1256,z4,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 505) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 505).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1016).take 375) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1391)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [505, 511, 375] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 147).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 147).take 152).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 299).take 149).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 448).take 64).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [147, 152, 149, 64] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38291

theorem PEqualNP.Outside.L_meta_38291 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 3974144160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 3974144160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38291.solve