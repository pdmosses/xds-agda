<pre class="Agda"><a id="1" class="Markup">\begin{code}</a>
<a id="14" class="Keyword">module</a> <a id="21" href="PCF.Variables.html" class="Module">PCF.Variables</a> <a id="35" class="Keyword">where</a>

<a id="42" class="Keyword">open</a> <a id="47" class="Keyword">import</a> <a id="54" href="Agda.Builtin.Nat.html" class="Module">Agda.Builtin.Nat</a>
  <a id="73" class="Keyword">using</a> <a id="79" class="Symbol">(</a><a id="80" href="Agda.Builtin.Nat.html#203" class="Datatype">Nat</a><a id="83" class="Symbol">)</a>

<a id="86" class="Keyword">open</a> <a id="91" class="Keyword">import</a> <a id="98" href="PCF.Types.html" class="Module">PCF.Types</a>
  <a id="110" class="Keyword">using</a> <a id="116" class="Symbol">(</a><a id="117" href="PCF.Types.html#196" class="Datatype">Types</a><a id="122" class="Symbol">;</a> <a id="124" href="PCF.Types.html#375" class="Generalizable">σ</a><a id="125" class="Symbol">;</a> <a id="127" href="PCF.Types.html#418" class="Function">𝒟</a><a id="128" class="Symbol">)</a>

<a id="131" class="Comment">-- Syntax</a>

<a id="142" class="Keyword">data</a> <a id="𝒱"></a><a id="147" href="PCF.Variables.html#147" class="Datatype">𝒱</a> <a id="149" class="Symbol">:</a> <a id="151" href="PCF.Types.html#196" class="Datatype">Types</a> <a id="157" class="Symbol">→</a> <a id="159" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="163" class="Keyword">where</a>
  <a id="𝒱.var"></a><a id="171" href="PCF.Variables.html#171" class="InductiveConstructor">var</a> <a id="175" class="Symbol">:</a> <a id="177" href="Agda.Builtin.Nat.html#203" class="Datatype">Nat</a> <a id="181" class="Symbol">→</a> <a id="183" class="Symbol">(</a><a id="184" href="PCF.Variables.html#184" class="Bound">σ</a> <a id="186" class="Symbol">:</a> <a id="188" href="PCF.Types.html#196" class="Datatype">Types</a><a id="193" class="Symbol">)</a> <a id="195" class="Symbol">→</a> <a id="197" href="PCF.Variables.html#147" class="Datatype">𝒱</a> <a id="199" href="PCF.Variables.html#184" class="Bound">σ</a>

<a id="202" class="Keyword">variable</a> <a id="211" href="PCF.Variables.html#211" class="Generalizable">α</a> <a id="213" class="Symbol">:</a> <a id="215" href="PCF.Variables.html#147" class="Datatype">𝒱</a> <a id="217" href="PCF.Types.html#375" class="Generalizable">σ</a>

<a id="220" class="Comment">-- Environments</a>

<a id="Env"></a><a id="237" href="PCF.Variables.html#237" class="Function">Env</a> <a id="241" class="Symbol">=</a> <a id="243" class="Symbol">∀</a> <a id="245" class="Symbol">{</a><a id="246" href="PCF.Variables.html#246" class="Bound">σ</a><a id="247" class="Symbol">}</a> <a id="249" class="Symbol">→</a> <a id="251" href="PCF.Variables.html#147" class="Datatype">𝒱</a> <a id="253" href="PCF.Variables.html#246" class="Bound">σ</a> <a id="255" class="Symbol">→</a> <a id="257" href="PCF.Types.html#418" class="Function">𝒟</a> <a id="259" href="PCF.Variables.html#246" class="Bound">σ</a>

<a id="262" class="Keyword">variable</a> <a id="271" href="PCF.Variables.html#271" class="Generalizable">ρ</a> <a id="273" class="Symbol">:</a> <a id="275" href="PCF.Variables.html#237" class="Function">Env</a>

<a id="280" class="Comment">-- Semantics</a>

<a id="_⟦_⟧"></a><a id="294" href="PCF.Variables.html#294" class="Function Operator">_⟦_⟧</a> <a id="299" class="Symbol">:</a> <a id="301" href="PCF.Variables.html#237" class="Function">Env</a> <a id="305" class="Symbol">→</a> <a id="307" href="PCF.Variables.html#147" class="Datatype">𝒱</a> <a id="309" href="PCF.Types.html#375" class="Generalizable">σ</a> <a id="311" class="Symbol">→</a> <a id="313" href="PCF.Types.html#418" class="Function">𝒟</a> <a id="315" href="PCF.Types.html#375" class="Generalizable">σ</a>

<a id="318" href="PCF.Variables.html#318" class="Bound">ρ</a> <a id="320" href="PCF.Variables.html#294" class="Function Operator">⟦</a> <a id="322" href="PCF.Variables.html#322" class="Bound">α</a> <a id="324" href="PCF.Variables.html#294" class="Function Operator">⟧</a> <a id="326" class="Symbol">=</a> <a id="328" href="PCF.Variables.html#318" class="Bound">ρ</a> <a id="330" href="PCF.Variables.html#322" class="Bound">α</a>
<a id="332" class="Markup">\end{code}</a></pre>