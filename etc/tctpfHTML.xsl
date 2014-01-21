<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                xmlns:exsl="http://exslt.org/common"
		xmlns:m="http://www.w3.org/1998/Math/MathML"
		xmlns:tct="http://cl-informatik.uibk.ac.at/software/tct"
		xmlns="http://www.w3.org/1999/xhtml"
                extension-element-prefixes="exsl"
                version="1.0">
    <xsl:output method="xml"
		doctype-system="http://www.w3.org/TR/xhtml1/DTD/xhtml11.dtd" 
		doctype-public="-//W3C//DTD XHTML 1.1 Transitional//EN" indent="yes"/>

    <xsl:strip-space elements="*"/>

    <xsl:include href="tctpfNORM.xsl"/>
    
    <xsl:variable name="reducedProofTree">
      <xsl:apply-templates select="/tctOutput/proofNode" mode="filter"/>
    </xsl:variable>
    

    <xsl:template match="/tctOutput">
      <html xmlns="http://www.w3.org/1999/xhtml"
	    xmlns:m="http://www.w3.org/1998/Math/MathML">
            <head>
                <title>Tct Output</title>
		<meta http-equiv="Content-Type" content="application/xhtml+xml; charset=utf-8" />
                <link rel="stylesheet" type="text/css" href="http://cl-informatik.uibk.ac.at/software/tct/includes/tct-output.css"/>
            </head>
            <body style="max-width:800px;">
	      <h1>Outline</h1>
	      <div class="outline">
	      	<xsl:apply-templates select="exsl:node-set($reducedProofTree)/proofNode">
	      	  <xsl:with-param name="outline">true</xsl:with-param>
	      	  <xsl:with-param name="number">1</xsl:with-param>
	      	  <xsl:with-param name="prefix"></xsl:with-param>
	      	</xsl:apply-templates>
	      </div>
	      <div class="proof">
	      	<h1>Input Problem</h1>
	      	We consider the <xsl:apply-templates select="proofNode/complexityInput"/>
		
	      	<h2>Proof Output</h2>
	      	<xsl:apply-templates select="exsl:node-set($reducedProofTree)/proofNode">
	      	  <xsl:with-param name="number">1</xsl:with-param>
	      	  <xsl:with-param name="prefix"></xsl:with-param>
	      	</xsl:apply-templates>
	      </div>
	    </body>
	</html>
    </xsl:template>

    <xsl:template name="sectionnumber">
      <xsl:param name="prefix"/>
      <xsl:param name="number"/>

      <xsl:choose>
	<xsl:when test="$prefix=''">
	  <xsl:value-of select="$number"/>
	</xsl:when>
	<xsl:otherwise>
	  <xsl:value-of select="concat(concat($prefix,'.'),$number)"/>
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>

    <!-- extract names -->

    <xsl:template match="proofNode" mode="processorName">
      <xsl:apply-templates select="proofDetail/*[1]" mode="processorName"/>
    </xsl:template>

    <xsl:template match="empty" mode="processorName">
      empty
    </xsl:template>


    <xsl:template match="success" mode="processorName">
      success
    </xsl:template>
    <xsl:template match="order" mode="processorName">
      <xsl:choose>
	<xsl:when test="compatible/interpretation/type">
	  <xsl:apply-templates select="compatible/interpretation/type"/>
	</xsl:when>
	<xsl:otherwise>
	  interpretation
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>

    <xsl:template match="transformation" mode="processorName">
      <xsl:choose>
	<xsl:when test="transformationDetail/noprogress">
	  <xsl:apply-templates select="transformationDetail/subProofs/*[1]" mode="processorName"/>
	</xsl:when>
	<xsl:when test="transformationDetail/simpPE">
	  predecessor estimation
	</xsl:when>
	<xsl:when test="transformationDetail/simpRHS">
	  simplify DP RHSs
	</xsl:when>
	<xsl:when test="transformationDetail/removetails">
	  remove tails
	</xsl:when>
	<xsl:when test="transformationDetail/removehead">
	  remove heads
	</xsl:when>
	<xsl:when test="transformationDetail/trivial">
	  trivial
	</xsl:when>
	<xsl:when test="transformationDetail/removeInapplicable">
	  remove inapplicable
	</xsl:when>
	<xsl:when test="transformationDetail/usablerules">
	  usable rules
	</xsl:when>
	<xsl:when test="transformationDetail/weightgap">
	  weight gap principle
	</xsl:when>
	<xsl:when test="transformationDetail/pathanalysis">
	  <xsl:value-of select="transformationDetail/pathanalysis/kind"/> path analysis
	</xsl:when>
	<xsl:when test="transformationDetail/decomposeDG">
	  DG decomposition
	</xsl:when>
	<xsl:when test="transformationDetail/dp">
	  <xsl:choose>
	    <xsl:when test="transformationDetail/dp/pairs">weak dependency pairs</xsl:when>
	    <xsl:when test="transformationDetail/dp/tuples">dependency tuples</xsl:when>
	    <xsl:otherwise>dependency pairs or tuples</xsl:otherwise>
	  </xsl:choose>
	</xsl:when>
	<xsl:otherwise>
	  unknown
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>


    <!-- proof drawing -->

    <xsl:template match="proofNode">
      <xsl:param name="number"/>
      <xsl:param name="prefix"/>
      <xsl:param name="up"/>
      <xsl:param name="outline">false</xsl:param>
      <xsl:param name="newsection">false</xsl:param>
      <xsl:variable name="id">
	<xsl:call-template name="sectionnumber">
	  <xsl:with-param name="prefix" select="$prefix"/>
	  <xsl:with-param name="number" select="$number"/>
	</xsl:call-template>
      </xsl:variable>

      <xsl:choose>
	<xsl:when test="$outline='true'">
	  <div class ="outline-item">
	    <span class="outline-link"><a><xsl:attribute name="href">#<xsl:value-of select="$id"/></xsl:attribute><xsl:value-of select="$id"/></a></span>
	    <span class="outline-processor"><xsl:apply-templates select="." mode="processorName"/></span>
	    <span class="outline-answer"><xsl:apply-templates select="complexityInput/answer"/></span>
	  </div>
	</xsl:when>
	<xsl:otherwise>
	  <h3>
	    <a> 
	      <xsl:attribute name="name"><xsl:value-of select="$id"/></xsl:attribute>
	    </a>
	    Proof Step <xsl:value-of select="$id"/> (<xsl:apply-templates select="." mode="processorName"/>)
	  </h3>
	  <a><xsl:attribute name="href">#<xsl:value-of select="$up"/></xsl:attribute> back</a>
	  <div class="complexityInput">
	    We consider the <xsl:apply-templates select="complexityInput"/>
	  </div>
	  TcT provides the certificate
	  <xsl:apply-templates select="complexityInput/answer"/> on above problem.
	</xsl:otherwise>
      </xsl:choose>
      
      <xsl:if test="count(proofDetail/transformation)>0 or $outline='false'">
	<xsl:choose>
	  <xsl:when test="$newsection='true'">
	    <xsl:apply-templates select="proofDetail/*[1]">
	      <xsl:with-param name="outline" select="$outline"/>
	      <xsl:with-param name="prefix" select="concat(concat($prefix,'.'),$number)"/>
	      <xsl:with-param name="number" select="0"/>
	    </xsl:apply-templates>
	  </xsl:when>
	  <xsl:otherwise>
	    <xsl:apply-templates select="proofDetail/*[1]">
	      <xsl:with-param name="outline" select="$outline"/>
	      <xsl:with-param name="prefix" select="$prefix"/>
	      <xsl:with-param name="up" select="$up"/>
	      <xsl:with-param name="number" select="$number"/>
	    </xsl:apply-templates>
	  </xsl:otherwise>
	</xsl:choose>      
      </xsl:if>
    </xsl:template>

    
    
    <!-- processor proofs -->

    
    <xsl:template match="oneOf">
      <xsl:param name="number"/>
      <xsl:param name="prefix"/>

      <xsl:choose>
	<!-- success -->
	<xsl:when test="subProof">
	  <xsl:apply-templates select="subProof/proofNode">
	    <xsl:with-param name="prefix" select="$prefix"/>
	    <xsl:with-param name="number" select="$number"/>
	    <xsl:with-param name="up" select="$up"/>
	  </xsl:apply-templates>
	</xsl:when>

	<!-- failure -->
	<xsl:otherwise>
	  <xsl:for-each select="failures">
	    Non of the processors succeeded on the problem.
	    <div class="indent">
	      <h3>Failed Attempt <xsl:value-of select="$number"/></h3>
	      <xsl:apply-templates select="proofNode">
		<xsl:with-param name="prefix" select="''"/>
		<xsl:with-param name="number"><xsl:number/></xsl:with-param>
	      </xsl:apply-templates>
	    </div>
	  </xsl:for-each>
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>

    <xsl:template match="transformation">
      <xsl:param name="number"/>
      <xsl:param name="prefix"/>
      <xsl:param name="outline">false</xsl:param>
      <xsl:if test="$outline='false'">
	<p>
	  <xsl:apply-templates select="transformationDetail/*">
	    <xsl:with-param name="prefix" select="$prefix"/>
	    <xsl:with-param name="number" select="$number"/>
	  </xsl:apply-templates>
	</p>
      </xsl:if>
      <xsl:choose>
      	<xsl:when test="count(subProofs/proofNode) = 0 and $outline='false'">
      	  The transformation did not result in further sub-problems.
      	</xsl:when>

      	<xsl:when test="count(subProofs/proofNode) = 1">
	  <xsl:apply-templates select="subProofs/proofNode">
	    <xsl:with-param name="prefix" select="$prefix"/>
	    <xsl:with-param name="number" select="$number + 1"/>
	    <xsl:with-param name="up" select="$number"/>
	    <xsl:with-param name="outline" select="$outline"/>	    
	  </xsl:apply-templates>
      	</xsl:when>

      	<xsl:otherwise>
	  <xsl:if test="$outline='false'">
	    The transformation results in <xsl:value-of select="count(subProofs/proofNode)"/> new problems.
	    Overall TcT provides the certificate
	    <xsl:apply-templates select="complexityInput/answer"/>, 
	    which is obtained obtained by combination of the following proofs.
	  </xsl:if>
	  <xsl:variable name="pref">
	    <xsl:call-template name="sectionnumber">
	      <xsl:with-param name="prefix" select="$prefix"/>
	      <xsl:with-param name="number" select="$number"/>
	    </xsl:call-template>
	  </xsl:variable>

	  <xsl:for-each select="subProofs/proofNode">
	    <div class="indent">
	      <xsl:apply-templates select=".">
		<xsl:with-param name="prefix" select="$pref"/>
		<xsl:with-param name ="up" select="$prefix"/>
		<xsl:with-param name="number" select="position()"/>
		<xsl:with-param name="newsection" select="'true'"/>
		<xsl:with-param name="outline" select="$outline"/>	    
	      </xsl:apply-templates>
	    </div>
	  </xsl:for-each>
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>


    <xsl:template match ="*/proofdata">
      <pre>
	<xsl:value-of select="."/>
      </pre>
    </xsl:template>


    <xsl:template match="order">
      <xsl:choose>
	<xsl:when test="compatible">
	  TcT found the following compatible 
	  <xsl:apply-templates select="compatible/interpretation"/>
	</xsl:when>
	<xsl:otherwise>
	  <xsl:text>TcT cound not find any compatible order.</xsl:text>
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>

    <!-- transformation proofs -->


    <xsl:template match="*/dperror">
      <xsl:choose>
	<xsl:when test="*/dperror/nodpproblem">
	  <xsl:text>The input problem is not a DP-problem.</xsl:text>
	</xsl:when>
	<xsl:when test="*/dperror/norcproblem">
	  <xsl:text>The input problem is not an RC-problem.</xsl:text>
	</xsl:when>
	<xsl:when test="*/dperror/notapplicable">
	  <xsl:text>The processor is inapplicable:</xsl:text>
	</xsl:when>
	<xsl:when test="*/dperror/containsstrictrule">
	  <xsl:text>The strict component is not empty.</xsl:text>
	</xsl:when>
      </xsl:choose>
      <xsl:text>The processor is not applicable.</xsl:text>
    </xsl:template>

    <xsl:template match="simpPE">

    </xsl:template>

    <xsl:template match="dp">
      <xsl:variable name="dps">
	<tct:ruleset>
	  <tct:strict>
	    <xsl:copy-of select="strictDPs/rules/*"/>
	  </tct:strict>
	  <weak>
	    <xsl:copy-of select="weakDPs/rules/*"/>
	  </weak>
	</tct:ruleset>
      </xsl:variable>
      <xsl:text>We add following dependency</xsl:text>
      <xsl:choose>
	<xsl:when test="pairs">pairs</xsl:when>
	<xsl:when test="tuples">tuples</xsl:when>
      </xsl:choose>
      <xsl:apply-templates select="exsl:node-set($dps)/*"/>
      <xsl:text>and adapt the set of starting terms appropriately.</xsl:text>
    </xsl:template>

    <xsl:template match="simpRHS">
      <xsl:apply-templates select="dependencygraph"/>
    </xsl:template>
    
    <xsl:template match="usablerules">
      <xsl:variable name="urs">
	<tct:ruleset>
	  <tct:strict>
	    <xsl:copy-of select="strict/rules/*"/>
	  </tct:strict>
	  <weak>
	    <xsl:copy-of select="weak/rules/*"/>
	  </weak>
	</tct:ruleset>
      </xsl:variable>
      <xsl:text>We replace rewrite rules by the following usable rules</xsl:text>
      <xsl:apply-templates select="exsl:node-set($urs)/*"/>      
    </xsl:template>


    <xsl:template match="pathanalysis">
      <xsl:text>We analyse paths trough the following dependency graph separately:</xsl:text>
      <p>
      <xsl:apply-templates select="dependencygraph"/>
      </p>
    </xsl:template>

    
    <xsl:template match="weightgap">
      <div class="indent">
      <xsl:text>The weight-gap principle applies, using the following </xsl:text>
      <xsl:apply-templates select="*[1]"/>
      </div>
    </xsl:template>
    
    <!-- input problem  -->

    <xsl:template match="complexityInput">
      <b>
	<xsl:if test="strategy/innermost">innermost </xsl:if>
	<xsl:apply-templates select="complexityMeasure"></xsl:apply-templates>
      </b>
      with respect to the 
      <xsl:apply-templates select="relation"/>
      <xsl:choose>
	<xsl:when test="complexityMeasure/runtimeComplexity">
	  Here defined symbols 
	  <xsl:for-each select="complexityMeasure/runtimeComplexity/signature[2]/symbol">
	    <xsl:if test="position() != 1">, </xsl:if>
	    <xsl:apply-templates select="*[1]"/>
	  </xsl:for-each>
	  and constructors 
	  <xsl:for-each select="complexityMeasure/runtimeComplexity/signature[1]/symbol">
	    <xsl:if test="position() != 1">, </xsl:if>
	    <xsl:apply-templates select="*[1]"/>
	  </xsl:for-each>
	  are considered.
	</xsl:when>
      </xsl:choose>            
    </xsl:template>

    <xsl:template match="complexityMeasure">
      <xsl:choose>
	<xsl:when test="derivationalComplexity">
	    derivational complexity
	</xsl:when>
	<xsl:when test="runtimeComplexity">
	  runtime complexity
	</xsl:when>
      </xsl:choose>            
    </xsl:template>

    <xsl:template match="answer">
      <xsl:choose>
	<xsl:when test="no"><span class="no">NO</span></xsl:when>
	<xsl:when test="maybe"><span class="maybe">MAYBE</span></xsl:when>
	<xsl:when test="timeout"><span class="timeout">TIMEOUT</span></xsl:when>
	<xsl:when test="certified">
	  <span class="yes">
	    YES(<xsl:apply-templates select="certified/lowerbound" mode="complexity_class"/>,
	    <xsl:apply-templates select="certified/upperbound" mode="complexity_class"/>)
	  </span>
	</xsl:when>
      </xsl:choose>
    </xsl:template>

    <xsl:template mode="complexity_class" match="polynomial">
        <xsl:choose>
            <xsl:when test="text() = 0">O(1)</xsl:when>
            <xsl:when test="text() = 1">O(n)</xsl:when>
            <xsl:otherwise>O(n<sup><xsl:value-of select="text()"/></sup>)</xsl:otherwise>
        </xsl:choose>        
    </xsl:template>

    <xsl:template mode="complexity_class" match="unknown">?</xsl:template>


    <xsl:template match="relation">
      <xsl:choose>
	<xsl:when test="strictDPs or weakDPs or strictTrs or weakTrs">
	  <xsl:choose>
	    <xsl:when test="strictDPs or weakDPs">
	      dependency pairs 
	      <xsl:variable name="dps">
		<tct:ruleset>
		  <tct:strict>
		    <xsl:copy-of select="strictDPs/rules/*"/>
		  </tct:strict>
		  <tct:weak>
		    <xsl:copy-of select="weakDPs/rules/*"/>
		  </tct:weak>
		</tct:ruleset>
	      </xsl:variable>
	      <xsl:apply-templates select="exsl:node-set($dps)/*"/>
	      <xsl:if test="strictTrs or weakTrs">
		together with the rewrite rules
	      </xsl:if>
	    </xsl:when>
	    <xsl:otherwise>
	  rewrite rules
	    </xsl:otherwise>
	  </xsl:choose>
	  <xsl:if test="strictTrs or weakTrs">
	    <xsl:variable name="rules">
	      <tct:ruleset>
		<tct:strict>
		  <xsl:copy-of select="strictTrs/rules/*"/>
		</tct:strict>
		<tct:weak>
		  <xsl:copy-of select="weakTrs/rules/*"/>
		</tct:weak>
	      </tct:ruleset>
	    </xsl:variable>
	    <xsl:apply-templates select="exsl:node-set($rules)/*"/>
	  </xsl:if>
	</xsl:when>
	<xsl:otherwise>
	  empty set of rewrite rules.
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>

    <xsl:template match="tct:ruleset">
      <p>
      <table class="ruleset">
	<xsl:variable name="strict">
	  <tct:rules>
	    <xsl:copy-of select="tct:strict/*"/>
	  </tct:rules>
	</xsl:variable>
	<xsl:variable name="weak">
	  <tct:rules>
	    <xsl:copy-of select="tct:weak/*"/>
	  </tct:rules>
	</xsl:variable>
	<xsl:apply-templates select="exsl:node-set($strict)/*">
	  <xsl:with-param name="strict">true</xsl:with-param>
	</xsl:apply-templates>
	<xsl:apply-templates select="exsl:node-set($weak)/*">		
	  <xsl:with-param name="strict">false</xsl:with-param>
	</xsl:apply-templates>		  
      </table>
      </p>
    </xsl:template>

    <xsl:template match="tct:rules">
        <xsl:param name="strict">true</xsl:param>
	<xsl:for-each select="*">
	      <tr>
		<td align="right"  class="rule-id">
		  <xsl:if test="@rid">
		    <xsl:value-of select="@rid"/>:
		  </xsl:if>
		</td>	    
		<td align="right" class="rule-lhs">
		  <xsl:apply-templates select="lhs"/>
		</td>
		<td align="center" class="rule-arr">
		  &#160;&#8594;<xsl:if test="$strict = 'false'"><sup>=</sup></xsl:if>&#160;
		</td>
		<td align="left" class="rule-rhs">
		  <xsl:apply-templates select="rhs"/>
		</td>
	      </tr>
	    </xsl:for-each>
    </xsl:template>

    <xsl:template match="lhs">
      <xsl:apply-templates select="*[1]"/>
    </xsl:template>

    <xsl:template match="rhs">
      <xsl:apply-templates select="*[1]"/>
    </xsl:template>
    <!-- misc objects -->

    <xsl:template match="dependencygraph">
      <xsl:variable name="dps">
	<tct:ruleset>
	  <tct:strict>
	    <xsl:copy-of select="nodes/*"/>
	  </tct:strict>
	</tct:ruleset>
      </xsl:variable>
      <!-- <xsl:variable name="thesvg"> -->
      <!-- 	<xsl:value-of select="svg" disable-output-escaping="yes" /> -->
      <!-- </xsl:variable> -->
      <div class="dependencygraph">
	<!-- <div class="dg-svg"> -->
	<!--   <xsl:copy-of select="exsl:node-set($thesvg)"/> -->
	<!-- </div> -->
	<!-- <div class="dg-nodes"> -->
	<!--   Here nodes are as follows: -->
	<!--   <xsl:apply-templates select="exsl:node-set($dps)"/> -->
	<!-- </div> -->
	<div class="dg-edges">
	  <xsl:choose>
	    <xsl:when test="count(edges)=0">
	      We consider a dependency graph without eges.
	      The graph contains no edges.
	    </xsl:when>
	    <xsl:otherwise>
	      We consider a dependency graph with edges:
	      <xsl:for-each select="edges/edge">
		<xsl:if test="count(target) > 0">
		  <div class="dg-source">
		    from
		    <xsl:variable name="src"><xsl:value-of select="source"/></xsl:variable>
		    (<xsl:value-of select="$src"/>)
		    <xsl:apply-templates select="../../nodes/rule[@rid=$src]/lhs"/>&#160;&#8594;&#160;
		    <xsl:apply-templates select="../../nodes/rule[@rid=$src]/rhs"/>
		    <div class="dg-targets">
		      <xsl:for-each select="target">
			<div class="dg-target">
			  <xsl:variable name="trg"><xsl:value-of select="."/></xsl:variable>
			  <xsl:choose>
			    <xsl:when test="position() = 1">to </xsl:when>
			    <xsl:when test="position() = last()">and </xsl:when>
			    <xsl:otherwise>, </xsl:otherwise>
			  </xsl:choose>
			  (<xsl:value-of select="$trg"/>)
			  <xsl:apply-templates select="../../../nodes/rule[@rid=$trg]/lhs"/>&#160;&#8594;&#160;
			  <xsl:apply-templates select="../../../nodes/rule[@rid=$trg]/rhs"/>
			</div>
		      </xsl:for-each>
		    </div>
		  </div>
		</xsl:if>
	      </xsl:for-each>
	    </xsl:otherwise>
	  </xsl:choose>
	</div>
      </div>
    </xsl:template>

    <!-- interpretations -->

    <xsl:template name="genVars">
      <xsl:param name="n"/>
      <xsl:choose>
	<xsl:when test="$n = 0"/>
	<xsl:when test="$n = 1">
	  <xsl:text>(</xsl:text><span class="var">x<sub>1</sub></span><xsl:text>)</xsl:text>
	</xsl:when>
	<xsl:when test="$n = 2">
	  <xsl:text>(</xsl:text><span class="var">x<sub>1</sub></span>, <span class="var">x<sub>2</sub></span><xsl:text>)</xsl:text>
	</xsl:when>
	<xsl:when test="$n = 3">
	  <xsl:text>(</xsl:text><span class="var">x<sub>1</sub></span>, <span class="var">x<sub>2</sub></span>, <span class="var">x<sub>3</sub></span><xsl:text>)</xsl:text>
	</xsl:when>
	<xsl:otherwise>
	  <xsl:text>(</xsl:text><span class="var">x<sub>1</sub></span>,...,<span class="var">x<sub><xsl:value-of select="$n"/></sub></span><xsl:text>)</xsl:text>
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>

    <xsl:template match="polynomial">
      <xsl:param name="inner">false</xsl:param>
	<xsl:choose>
	  <xsl:when test="coefficient">
	    <xsl:apply-templates select="coefficient"/>
	  </xsl:when>
	  <xsl:when test="variable">
	      <m:mrow>
		<msub class="var">
		  <m:mn>x</m:mn>
		  <m:mn><xsl:value-of select="variable/text()"/></m:mn>
		</msub>
	      </m:mrow>
	  </xsl:when>
	  <xsl:when test="sum">
	    <m:mrow>
	      <xsl:if test="$inner = 'true'">
		<m:mo>(</m:mo>                    
	      </xsl:if>
	      <xsl:for-each select="sum/polynomial">
		<xsl:apply-templates select="."/>
		<xsl:if test="position() != last()"><m:mo>+</m:mo></xsl:if>                    
	      </xsl:for-each>
	      <xsl:if test="$inner = 'true'">
		<m:mo>)</m:mo>
	      </xsl:if>
	    </m:mrow>
	  </xsl:when>
	  <xsl:when test="product">
	    <m:mrow>
	      <xsl:for-each select="product/polynomial">
		<xsl:apply-templates select=".">
		  <xsl:with-param name="inner">true</xsl:with-param>
		</xsl:apply-templates>
		<xsl:if test="position() != last()"> <m:mo>&#183;</m:mo></xsl:if>
	      </xsl:for-each>
	    </m:mrow>
	  </xsl:when>
	  <xsl:when test="max">
	    <m:mrow>
	      <m:mi>max</m:mi>
	      <m:mo stretchy="false">(</m:mo>
	      <xsl:for-each select="max/polynomial">
		<xsl:apply-templates select="."/>
		<xsl:if test="position() != last()"><m:mi>,</m:mi></xsl:if>
	      </xsl:for-each>
	      <m:mo stretchy="false">)</m:mo>
	    </m:mrow>
	  </xsl:when>
	  <xsl:when test="min">
	    <m:mrow>
	      <m:mi>min</m:mi>
	      <m:mo stretchy="false">(</m:mo>
	      <xsl:for-each select="min/polynomial">
		<xsl:apply-templates select="."/>
		<xsl:if test="position() != last()"><m:mi>,</m:mi></xsl:if>
	      </xsl:for-each>
	      <m:mo stretchy="false">)</m:mo>
	    </m:mrow>
	  </xsl:when>
	  <xsl:otherwise>unknown polynomial type</xsl:otherwise>
	</xsl:choose>
    </xsl:template>

    
    <xsl:template match="integer">
      <m:mn>
	<xsl:value-of select="text()"/>
      </m:mn>
    </xsl:template>
    
    <xsl:template match="rational">
      <m:mrow>
	<xsl:variable name="denom" select="denominator/text()"/>
	<xsl:choose>
	  <xsl:when test="$denom != 1">
	    <m:mfrac>
	      <m:mn>
		<xsl:value-of select="numerator/text()"/>	
	      </m:mn>
	      <m:mn>
		<xsl:value-of select="$denom"/>
	      </m:mn>
	    </m:mfrac>
	  </xsl:when>
	  <xsl:otherwise>
	    <m:mn>
	      <xsl:value-of select="numerator/text()"/>	
	    </m:mn>
	  </xsl:otherwise>
	</xsl:choose>
      </m:mrow>
    </xsl:template>    

    <xsl:template match="vector">
        <xsl:choose>
	  <xsl:when test="count(coefficient) = 0"><m:mo stretchy="false">(</m:mo><m:mo stretchy="false">)</m:mo></xsl:when>
	  <xsl:otherwise>
	    <m:mrow>
	      <m:mo>[</m:mo>
	      <m:mtable>
		<xsl:for-each select="coefficient">
		  <m:mtr>
		    <m:mtd columnalign="center">
		      <m:mrow>
			<xsl:apply-templates select="."/>
		      </m:mrow>
		    </m:mtd>
		  </m:mtr>
		</xsl:for-each>
	      </m:mtable>
	      <m:mo>]</m:mo>
	    </m:mrow>
	  </xsl:otherwise>
        </xsl:choose>
    </xsl:template>
    
    <xsl:template match="matrix">
        <xsl:choose>
            <xsl:when test="count(vector) = 0">()</xsl:when>
            <xsl:otherwise>
	      <m:mrow>
		<m:mo>[</m:mo>
		<m:mtable>
		  <xsl:call-template name="matrix2">
		    <xsl:with-param name="width" select="count(vector)"/>
		    <xsl:with-param name="heigth" select="count(vector[1]/coefficient)"/>
		    <xsl:with-param name="h" select="1"/>
		  </xsl:call-template>
		</m:mtable>
		<m:mo>]</m:mo>
	      </m:mrow>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>
    
    <xsl:template name="matrix2">
      <xsl:param name="heigth"/>
      <xsl:param name="width"/>
      <xsl:param name="h"/>
      <m:mtr>
	<xsl:call-template name="matrix3">
	  <xsl:with-param name="width" select="$width"/>
	  <xsl:with-param name="h" select="$h"/>                
	  <xsl:with-param name="w" select="1"/>                
	</xsl:call-template>
      </m:mtr>
      <xsl:if test="$h != $heigth">
	<xsl:call-template name="matrix2">
	  <xsl:with-param name="heigth" select="$heigth"/>
	  <xsl:with-param name="width" select="$width"/>
	  <xsl:with-param name="h" select="$h + 1"/>
	</xsl:call-template>
      </xsl:if>
    </xsl:template>

    <xsl:template name="matrix3">
      <xsl:param name="width"/>
      <xsl:param name="h"/>
      <xsl:param name="w"/>
      <m:mtd>
	<m:mn>
	  <xsl:apply-templates select="vector[$w]/coefficient[$h]"/>
	</m:mn>
      </m:mtd>
      <xsl:if test="$w != $width">
	<xsl:call-template name="matrix3">
	  <xsl:with-param name="width" select="$width"/>
	  <xsl:with-param name="w" select="$w + 1"/>
	  <xsl:with-param name="h" select="$h"/>
	</xsl:call-template>
      </xsl:if>
    </xsl:template>
    
    <xsl:template match="coefficient">        
      <xsl:choose>
	<xsl:when test="integer">
	  <xsl:apply-templates select="integer"/>
	</xsl:when>
	<xsl:when test="rational">
	  <xsl:apply-templates select="rational"/>
	</xsl:when>
	<xsl:when test="minusInfinity">
	  -&#8734;
	</xsl:when>
	<xsl:when test="vector">
	  <xsl:apply-templates select="vector"/>
	</xsl:when>
	<xsl:when test="matrix">
	  <xsl:apply-templates select="matrix"/>                
	</xsl:when>
	<xsl:otherwise>
	  unknown coefficient
	</xsl:otherwise>
      </xsl:choose>        
    </xsl:template>
    
    
    <xsl:template match="domain">
      <xsl:if test="naturals">the naturals</xsl:if>
      <xsl:if test="integers">the integers</xsl:if>
      <xsl:if test="arctic">the arctic semiring over <xsl:apply-templates select="arctic/domain"/></xsl:if>
      <xsl:if test="rationals">the rationals with delta = <xsl:apply-templates select="rationals/delta/*"/></xsl:if>
      <xsl:if test="arcticBelowZero">the integers with -&#8734; in the arctic semiring</xsl:if>
      <xsl:if test="matrices">(<xsl:value-of select="matrices/dimension/text()"/> x <xsl:value-of
      select="matrices/dimension/text()"/>)-matrices with strict dimension <xsl:value-of select="matrices/strictDimension/text()"/> 
      over <xsl:apply-templates
      select="matrices/domain"/>
      </xsl:if>
    </xsl:template>
    
    <xsl:template match="type">
      <!-- currently the strict dimensions are not displayed -->
      <xsl:choose>            
	<xsl:when test="polynomial">
	  <xsl:if test="polynomial/degree/text() != 1">non-</xsl:if>
	  <xsl:text>linear polynomial interpretation over </xsl:text>
	  <xsl:apply-templates select="polynomial/domain"/>
	</xsl:when>
	<xsl:when test="matrixInterpretation">
	  <xsl:text>matrix interpretations (dimension </xsl:text> 
	  <xsl:value-of select="matrixInterpretation/dimension/text()"/>
	  <xsl:text>) over </xsl:text>
	  <xsl:apply-templates select="matrixInterpretation/domain"/>            
	</xsl:when>
	<xsl:otherwise>
	  interpretations
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>
    
    <xsl:template match="interpretation">
      <xsl:apply-templates select="*[1]"/>
      <p>
	<m:math display='block'>
	  <m:mtable>
	    <xsl:for-each select="interpret">
	      <m:mtr>
		<m:mtd columnalign="right">
		  <m:mrow>
		    <m:mi>
		      <xsl:text>[</xsl:text>
		      <xsl:apply-templates select="*[1]"/>
		      <xsl:call-template name="genVars">
			<xsl:with-param name="n" select="arity"/>
		      </xsl:call-template>
		      <xsl:text>]</xsl:text>
		    </m:mi>
		  </m:mrow>
		</m:mtd>
		<m:mtd columnalign="center">
		  <m:mo>=</m:mo>
		</m:mtd>
		<m:mtd columnalign="left">		  
		  <xsl:apply-templates select="*[3]"/>
		</m:mtd>
	      </m:mtr>
	    </xsl:for-each>
	  </m:mtable>
	</m:math>
      </p>
    </xsl:template>


    <!-- terms -->

    <xsl:template match="funapp">
      <xsl:apply-templates select="*[1]"/>
      <xsl:if test="count(arg) &gt; 0">
      <xsl:text>(</xsl:text>
      <xsl:for-each select="arg">
        <xsl:apply-templates/>
        <xsl:if test="position() != last()">,</xsl:if>
      </xsl:for-each>
      <xsl:text>)</xsl:text>
      </xsl:if>
    </xsl:template>

    <xsl:template name="var" match="var">
        <span class="var"><xsl:value-of select="."/></span>
    </xsl:template>

    <xsl:template match="sharp">
        <span class="dp_fun">
            <xsl:apply-templates select="*[1]">
                <xsl:with-param name="sharp">true</xsl:with-param>
            </xsl:apply-templates>
            <sup>#</sup>
        </span>        
    </xsl:template>

    <xsl:template match="name">
        <xsl:param name="sharp">false</xsl:param>
        <xsl:choose>
            <xsl:when test="$sharp = 'true'">
                <xsl:value-of select="text()"/>                
            </xsl:when>
            <xsl:otherwise>
                <span class="fun">
                    <xsl:value-of select="text()"/>
                </span>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>

    <xsl:template match="numberLabel">
        <span class="label">
            <xsl:apply-templates/>
        </span>
    </xsl:template>
    <xsl:template match="symbolLabel">
        <span class="label">
            <xsl:apply-templates/>
        </span>
    </xsl:template>
    
    <xsl:template match="labeledSymbol">
        <xsl:param name="sharp">false</xsl:param>
        <xsl:apply-templates select="*[1]">
            <xsl:with-param name="sharp" select="$sharp"/>
        </xsl:apply-templates>
        <sub>
            <xsl:apply-templates select="*[2]"/>
        </sub>
    </xsl:template>


    


</xsl:stylesheet>
