<pre class="Agda">
<a id="14" class="Keyword">module</a> <a id="21" href="ULC.Domains.html" class="Module">ULC.Domains</a> <a id="33" class="Keyword">where</a>

<a id="40" class="Keyword">open</a> <a id="45" class="Keyword">import</a> <a id="52" href="Function.html" class="Module">Function</a>
  <a id="63" class="Keyword">using</a> <a id="69" class="Symbol">(</a><a id="70" href="Function.Bundles.html#7340" class="Record">Inverse</a><a id="77" class="Symbol">;</a> <a id="79" href="Function.Bundles.html#12701" class="Function Operator">_↔_</a><a id="82" class="Symbol">)</a> <a id="84" class="Keyword">public</a>
<a id="91" class="Keyword">open</a> <a id="96" href="Function.Bundles.html#7340" class="Module">Inverse</a> <a id="104" class="Symbol">{{</a> <a id="107" class="Symbol">...</a> <a id="111" class="Symbol">}}</a>
  <a id="116" class="Keyword">using</a> <a id="122" class="Symbol">(</a><a id="123" href="Function.Bundles.html#7394" class="Field">to</a><a id="125" class="Symbol">;</a> <a id="127" href="Function.Bundles.html#7418" class="Field">from</a><a id="131" class="Symbol">)</a> <a id="133" class="Keyword">public</a>

<a id="141" class="Keyword">postulate</a>   <a id="153" class="Comment">-- unsound!</a>
  <a id="D∞"></a><a id="167" href="ULC.Domains.html#167" class="Postulate">D∞</a> <a id="170" class="Symbol">:</a> <a id="172" href="Agda.Primitive.html#388" class="Primitive">Set</a>
  <a id="178" class="Keyword">instance</a>  <a id="iso"></a><a id="188" href="ULC.Domains.html#188" class="Postulate">iso</a> <a id="192" class="Symbol">:</a> <a id="194" href="ULC.Domains.html#167" class="Postulate">D∞</a> <a id="197" href="Function.Bundles.html#12701" class="Function Operator">↔</a> <a id="199" class="Symbol">(</a><a id="200" href="ULC.Domains.html#167" class="Postulate">D∞</a> <a id="203" class="Symbol">→</a> <a id="205" href="ULC.Domains.html#167" class="Postulate">D∞</a><a id="207" class="Symbol">)</a>

<a id="210" class="Keyword">variable</a> <a id="219" href="ULC.Domains.html#219" class="Generalizable">d</a> <a id="221" class="Symbol">:</a> <a id="223" href="ULC.Domains.html#167" class="Postulate">D∞</a>
</pre> 