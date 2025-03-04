<pre class="Agda"><a id="1" class="Markup">\begin{code}</a>
<a id="14" class="Keyword">module</a> <a id="21" href="ULC.Terms.html" class="Module">ULC.Terms</a> <a id="31" class="Keyword">where</a>

<a id="38" class="Keyword">open</a> <a id="43" class="Keyword">import</a> <a id="50" href="ULC.Variables.html" class="Module">ULC.Variables</a>

<a id="65" class="Keyword">data</a> <a id="Exp"></a><a id="70" href="ULC.Terms.html#70" class="Datatype">Exp</a> <a id="74" class="Symbol">:</a> <a id="76" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="80" class="Keyword">where</a>
  <a id="Exp.var_"></a><a id="88" href="ULC.Terms.html#88" class="InductiveConstructor Operator">var_</a>  <a id="94" class="Symbol">:</a> <a id="96" href="ULC.Variables.html#123" class="Datatype">Var</a> <a id="100" class="Symbol">→</a> <a id="102" href="ULC.Terms.html#70" class="Datatype">Exp</a>         <a id="114" class="Comment">-- variable value</a>
  <a id="Exp.lam"></a><a id="134" href="ULC.Terms.html#134" class="InductiveConstructor">lam</a>   <a id="140" class="Symbol">:</a> <a id="142" href="ULC.Variables.html#123" class="Datatype">Var</a> <a id="146" class="Symbol">→</a> <a id="148" href="ULC.Terms.html#70" class="Datatype">Exp</a> <a id="152" class="Symbol">→</a> <a id="154" href="ULC.Terms.html#70" class="Datatype">Exp</a>   <a id="160" class="Comment">-- lambda abstraction</a>
  <a id="Exp.app"></a><a id="184" href="ULC.Terms.html#184" class="InductiveConstructor">app</a>   <a id="190" class="Symbol">:</a> <a id="192" href="ULC.Terms.html#70" class="Datatype">Exp</a> <a id="196" class="Symbol">→</a> <a id="198" href="ULC.Terms.html#70" class="Datatype">Exp</a> <a id="202" class="Symbol">→</a> <a id="204" href="ULC.Terms.html#70" class="Datatype">Exp</a>   <a id="210" class="Comment">-- application</a>

<a id="226" class="Keyword">variable</a> <a id="235" href="ULC.Terms.html#235" class="Generalizable">e</a> <a id="237" class="Symbol">:</a> <a id="239" href="ULC.Terms.html#70" class="Datatype">Exp</a>
<a id="243" class="Markup">\end{code}</a></pre>