# Style Guide for MVP4 Paper: "Renormalization Group Flow as Truth Predicate"

## Target Audience: HEP-TH/MATH-PH Readers

### Audience Characteristics
- **Background**: Strong in quantum field theory, renormalization, conformal field theory
- **Weaknesses**: Limited experience with formal logic, computational paradigms
- **Strengths**: Deep understanding of RG flow, beta functions, scaling, anomalies
- **Expectations**: Mathematical rigor, clear notation, physical intuition

## Writing Style Principles

### 1. Mathematical Rigor with Physical Intuition
- **Lead with physical intuition**, then provide mathematical precision
- **Use familiar QFT terminology** when possible (RG flow, beta functions, anomalies)
- **Define unfamiliar terms** (logic, computation) in familiar language
- **Provide concrete examples** before abstract definitions

### 2. Notation Consistency
- **Generating Function**: Always $G(z,\bar{z};q_1,q_2,q_3,\Lambda)$
- **Logic Transformer**: Always $\mathcal{T}$ (not $\mathsf{G}_6$)
- **Parameters**: $(q_1,q_2,q_3)$ for paradigms, $\Lambda$ for scale
- **States**: $|n,m\rangle$ for computational states, $|x,y\rangle$ for input/output
- **Operators**: $\hat{W}(\vec{q})$ for evolution operators

### 3. Section Structure Template
Each section should follow this structure:
```
1. Introduction (1-2 paragraphs)
   - What this section accomplishes
   - How it connects to previous sections
   - Preview of key results

2. Definitions (2-3 definitions)
   - Core mathematical objects
   - Explicit identifications with generating function
   - Physical interpretation

3. Main Results (1-2 theorems/propositions)
   - Mathematical statements
   - Proof sketches or intuition
   - Connection to RG flow

4. Examples/Applications (1-2 concrete examples)
   - Specific parameter choices
   - Explicit calculations
   - Physical interpretation

5. Transition (1 paragraph)
   - How this leads to next section
   - What questions remain
```

### 4. Mathematical Presentation Standards

#### Equations
- **Number all important equations** with descriptive labels
- **Use consistent notation** across all equations
- **Provide physical interpretation** for each equation
- **Show explicit identifications** with generating function

#### Definitions
- **Use standard LaTeX environments**: `\begin{definition}`, `\begin{theorem}`, `\begin{proof}`
- **Provide both mathematical and physical meaning**
- **Include explicit identifications** with generating function
- **Give concrete examples** when possible

#### Proofs
- **Provide proof sketches** rather than full proofs
- **Focus on intuition** rather than technical details
- **Connect to RG flow** whenever possible
- **Use familiar QFT techniques** (scaling, dimensional analysis)

### 5. Flow and Coherence

#### Between Sections
- **Explicit transitions**: Each section should begin by connecting to previous work
- **Progressive complexity**: Start simple, build complexity gradually
- **Consistent themes**: Always return to RG flow, generating function, logic transformer
- **Clear motivation**: Why is this section necessary?

#### Within Sections
- **Logical progression**: Each paragraph should follow naturally from the previous
- **Avoid statement-dumping**: Connect ideas with transitions
- **Use signposts**: "This leads to...", "We now show...", "The key insight is..."
- **Provide context**: Why is this result important?

### 6. Language and Tone

#### Technical Language
- **Use precise terminology** but explain unfamiliar terms
- **Avoid jargon** from logic/computation without explanation
- **Prefer active voice** over passive voice
- **Use present tense** for mathematical statements

#### Audience Adaptation
- **Start with familiar concepts** (RG flow, beta functions)
- **Introduce new concepts gradually** (logic, computation)
- **Provide physical analogies** for abstract concepts
- **Use QFT terminology** when possible

### 7. Specific Guidelines for Each Section

#### Section 1: Computation Paradigms
- **Start with familiar**: RG flow, scaling, beta functions
- **Introduce gradually**: Turing machines, lambda calculus, path integrals
- **Emphasize unity**: All paradigms follow same cycle
- **Provide concrete examples**: Specific calculations for each paradigm

#### Section 2: Regularization
- **Use QFT language**: Cutoffs, counterterms, bare parameters
- **Connect to familiar**: Dimensional regularization, minimal subtraction
- **Show explicit mappings**: How regulators map to generating function
- **Provide physical intuition**: Why regularization is necessary

#### Section 3: RG Flow
- **Leverage expertise**: This is familiar territory for HEP-TH readers
- **Emphasize novelty**: RG flow as truth predicate
- **Show explicit identifications**: How flow behavior maps to truth values
- **Provide concrete examples**: Specific flow equations

#### Section 4: Renormalization
- **Use standard QFT language**: Renormalization group equations, running parameters
- **Show explicit procedure**: Step-by-step renormalization
- **Connect to computation**: How renormalization applies to computation
- **Provide physical interpretation**: Information preservation, reversibility

#### Section 5: Formal Systems
- **Introduce gradually**: Start with familiar (formal power series), then logic
- **Use concrete examples**: Specific logical systems
- **Show explicit mappings**: How logic maps to generating function
- **Provide physical intuition**: Logic as computational dynamics

#### Section 6: Truth Fixed Point
- **Start with familiar**: Fixed points, stability, convergence
- **Introduce gradually**: Truth as fixed point
- **Show explicit identifications**: How truth maps to generating function
- **Provide physical intuition**: Truth as stable state

#### Section 7: Effective Logic
- **Use familiar concepts**: Hierarchies, effective theories
- **Introduce gradually**: Logic hierarchies
- **Show explicit mappings**: How hierarchies map to generating function
- **Provide physical intuition**: Logic as effective theory

#### Section 8: Consistency
- **Leverage expertise**: Conservation laws, Noether's theorem
- **Show explicit connections**: How conservation maps to generating function
- **Provide physical intuition**: Consistency as conservation
- **Connect to familiar**: Standard QFT conservation laws

#### Section 9: Boundary Maps
- **Use familiar concepts**: Holographic renormalization, AdS/CFT
- **Introduce gradually**: Self-boundary maps
- **Show explicit mappings**: How boundaries map to generating function
- **Provide physical intuition**: Boundaries as computational interfaces

#### Section 10: LLMs
- **Start with familiar**: Scaling laws, power laws
- **Introduce gradually**: Machine learning, neural networks
- **Show explicit mappings**: How LLMs map to generating function
- **Provide physical intuition**: LLMs as computational systems

#### Section 11: Spectral Gap
- **Leverage expertise**: Spectral theory, operator theory
- **Show explicit connections**: How spectral gap maps to generating function
- **Provide physical intuition**: Spectral gap as computational gap
- **Connect to familiar**: Standard spectral theory

### 8. Common Pitfalls to Avoid

#### Mathematical
- **Inconsistent notation**: Always use same symbols for same concepts
- **Missing identifications**: Always show how concepts map to generating function
- **Unclear definitions**: Always provide both mathematical and physical meaning
- **Missing examples**: Always provide concrete examples

#### Expository
- **Statement-dumping**: Always connect ideas with transitions
- **Missing motivation**: Always explain why results are important
- **Unclear flow**: Always show how sections connect
- **Missing context**: Always provide physical interpretation

#### Audience
- **Too much logic jargon**: Always explain unfamiliar terms
- **Too little QFT connection**: Always connect to familiar concepts
- **Missing physical intuition**: Always provide physical meaning
- **Unclear motivation**: Always explain why this matters

### 9. Quality Checklist

Before finalizing each section, check:
- [ ] **Notation consistency**: All symbols used consistently
- [ ] **Explicit identifications**: All concepts mapped to generating function
- [ ] **Physical intuition**: All mathematical concepts have physical meaning
- [ ] **Clear transitions**: Each paragraph flows naturally
- [ ] **Concrete examples**: Abstract concepts illustrated with examples
- [ ] **Audience adaptation**: Familiar concepts used when possible
- [ ] **Mathematical rigor**: All statements are mathematically precise
- [ ] **Coherence**: Section connects to overall narrative

### 10. Final Notes

- **Remember the audience**: HEP-TH readers are experts in QFT but novices in logic
- **Emphasize unity**: All concepts connect through generating function and RG flow
- **Provide intuition**: Mathematical rigor without physical meaning is insufficient
- **Maintain flow**: Each section should build naturally on previous work
- **Be explicit**: Don't assume readers will make connections automatically
