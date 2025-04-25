<pre class="Agda">
<a id="14" class="Keyword">module</a> <a id="21" href="PCF.Types.html" class="Module">PCF.Types</a> <a id="31" class="Keyword">where</a>

<a id="38" class="Keyword">open</a> <a id="43" class="Keyword">import</a> <a id="50" href="Data.Bool.Base.html" class="Module">Data.Bool.Base</a> 
  <a id="68" class="Keyword">using</a> <a id="74" class="Symbol">(</a><a id="75" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a><a id="79" class="Symbol">)</a>
<a id="81" class="Keyword">open</a> <a id="86" class="Keyword">import</a> <a id="93" href="Agda.Builtin.Nat.html" class="Module">Agda.Builtin.Nat</a>
  <a id="112" class="Keyword">using</a> <a id="118" class="Symbol">(</a><a id="119" href="Agda.Builtin.Nat.html#203" class="Datatype">Nat</a><a id="122" class="Symbol">)</a>

<a id="125" class="Keyword">open</a> <a id="130" class="Keyword">import</a> <a id="137" href="PCF.Domain-Notation.html" class="Module">PCF.Domain-Notation</a>
  <a id="159" class="Keyword">using</a> <a id="165" class="Symbol">(</a><a id="166" href="PCF.Domain-Notation.html#685" class="Function Operator">_+⊥</a><a id="169" class="Symbol">)</a>

<a id="172" class="Comment">-- Syntax</a>

<a id="183" class="Keyword">data</a> <a id="Types"></a><a id="188" href="PCF.Types.html#188" class="Datatype">Types</a> <a id="194" class="Symbol">:</a> <a id="196" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="200" class="Keyword">where</a>
  <a id="Types.ι"></a><a id="208" href="PCF.Types.html#208" class="InductiveConstructor">ι</a>    <a id="213" class="Symbol">:</a> <a id="215" href="PCF.Types.html#188" class="Datatype">Types</a>                  <a id="238" class="Comment">-- natural numbers</a>
  <a id="Types.o"></a><a id="259" href="PCF.Types.html#259" class="InductiveConstructor">o</a>    <a id="264" class="Symbol">:</a> <a id="266" href="PCF.Types.html#188" class="Datatype">Types</a>                  <a id="289" class="Comment">-- Boolean truthvalues</a>
  <a id="Types._⇒_"></a><a id="314" href="PCF.Types.html#314" class="InductiveConstructor Operator">_⇒_</a>  <a id="319" class="Symbol">:</a> <a id="321" href="PCF.Types.html#188" class="Datatype">Types</a> <a id="327" class="Symbol">→</a> <a id="329" href="PCF.Types.html#188" class="Datatype">Types</a> <a id="335" class="Symbol">→</a> <a id="337" href="PCF.Types.html#188" class="Datatype">Types</a>  <a id="344" class="Comment">-- functions</a>

<a id="358" class="Keyword">variable</a> <a id="367" href="PCF.Types.html#367" class="Generalizable">σ</a> <a id="369" href="PCF.Types.html#369" class="Generalizable">τ</a> <a id="371" class="Symbol">:</a> <a id="373" href="PCF.Types.html#188" class="Datatype">Types</a>

<a id="380" class="Keyword">infixr</a> <a id="387" class="Number">1</a> <a id="389" href="PCF.Types.html#314" class="InductiveConstructor Operator">_⇒_</a>

<a id="394" class="Comment">-- Semantics 𝒟</a>

<a id="𝒟"></a><a id="410" href="PCF.Types.html#410" class="Function">𝒟</a> <a id="412" class="Symbol">:</a> <a id="414" href="PCF.Types.html#188" class="Datatype">Types</a> <a id="420" class="Symbol">→</a> <a id="422" href="Agda.Primitive.html#388" class="Primitive">Set</a>  <a id="427" class="Comment">-- Set should be a sort of domains</a>

<a id="463" href="PCF.Types.html#410" class="Function">𝒟</a> <a id="465" href="PCF.Types.html#208" class="InductiveConstructor">ι</a>        <a id="474" class="Symbol">=</a> <a id="476" href="Agda.Builtin.Nat.html#203" class="Datatype">Nat</a>  <a id="481" href="PCF.Domain-Notation.html#685" class="Function Operator">+⊥</a>
<a id="484" href="PCF.Types.html#410" class="Function">𝒟</a> <a id="486" href="PCF.Types.html#259" class="InductiveConstructor">o</a>        <a id="495" class="Symbol">=</a> <a id="497" href="Agda.Builtin.Bool.html#173" class="Datatype">Bool</a> <a id="502" href="PCF.Domain-Notation.html#685" class="Function Operator">+⊥</a>
<a id="505" href="PCF.Types.html#410" class="Function">𝒟</a> <a id="507" class="Symbol">(</a><a id="508" href="PCF.Types.html#508" class="Bound">σ</a> <a id="510" href="PCF.Types.html#314" class="InductiveConstructor Operator">⇒</a> <a id="512" href="PCF.Types.html#512" class="Bound">τ</a><a id="513" class="Symbol">)</a>  <a id="516" class="Symbol">=</a> <a id="518" href="PCF.Types.html#410" class="Function">𝒟</a> <a id="520" href="PCF.Types.html#508" class="Bound">σ</a> <a id="522" class="Symbol">→</a> <a id="524" href="PCF.Types.html#410" class="Function">𝒟</a> <a id="526" href="PCF.Types.html#512" class="Bound">τ</a>

<a id="529" class="Keyword">variable</a> <a id="538" href="PCF.Types.html#538" class="Generalizable">x</a> <a id="540" href="PCF.Types.html#540" class="Generalizable">y</a> <a id="542" href="PCF.Types.html#542" class="Generalizable">z</a> <a id="544" class="Symbol">:</a> <a id="546" href="PCF.Types.html#410" class="Function">𝒟</a> <a id="548" href="PCF.Types.html#367" class="Generalizable">σ</a>
</pre>