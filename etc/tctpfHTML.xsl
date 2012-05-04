<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">
    <xsl:output method="html"/>
    <xsl:strip-space elements="*"/>
    
    <xsl:template match="/tctOutput">
        <html>
            <head>
                <title>
                    Tct Output
                </title>
		<link rel="stylesheet" type="text/css" href="stickytooltip.css" />
                <style rel="stylesheet" type="text/css">
                    .dp_fun { color: darkgreen; }
                    .error { color: red; }
                    .fun { color: darkblue; }
                    .label { color: gray; }
                    .var { color: red; }

		    .indent { 
		      margin-left: 1.0em;
		    }

		    .proofdata {
		      font-family	: monospace;
		      line-height	: normal;
		      padding-top	: 10px;
		      padding-bottom	: 10px;
		      padding-left	: 10px;
		      padding-right	: 10px;
		      display        : inline-block;
		      min-width      : 95%;
		      font-size      : 10pt;
		    }

		    .yes { 
		    color: #009900;        
		    font-style: italic;
		    }



		    .no { 
		    color: #00BB00;
		    font-style: italic;	
		    }

		    .maybe { 
		    color: #FF9900;
		    font-style: italic;
		    }

		    .timeout { 
		    color: #FFBB00; 
		    font-style: italic;
		    }

		    .matrix {
		    border-left: thin black solid;
		    border-right: thin black solid; 
		    }
                </style>
            </head>
            <body style="max-width:800px;">
		<h1>Input Problem</h1>
		We consider the <xsl:apply-templates select="proofNode/complexityInput"/>
		
		<h2>Proof Output</h2>
		<xsl:apply-templates select="proofNode">
		  <xsl:with-param name="number">1</xsl:with-param>
		  <xsl:with-param name="prefix"></xsl:with-param>
		</xsl:apply-templates>
	    </body>
	</html>
    </xsl:template>




    <xsl:template match="proofNode">
      <xsl:param name="number"/>
      <xsl:param name="prefix"/>
      <xsl:param name="proofOnly">true</xsl:param>
      <xsl:param name="subsection">false</xsl:param>

      <xsl:variable name="pref">
	<xsl:choose>
	  <xsl:when test="$subsection='true'">
	    <xsl:choose>
	      <xsl:when test="$prefix=''"><xsl:value-of select="$number"/></xsl:when>
	      <xsl:otherwise><xsl:value-of select="concat(concat($prefix,'.'),$number)"/></xsl:otherwise>
	    </xsl:choose>
	  </xsl:when>
	  <xsl:otherwise><xsl:value-of select="$prefix"/></xsl:otherwise>
	</xsl:choose>
      </xsl:variable>

      <xsl:variable name="num">
	<xsl:choose>
	  <xsl:when test="$subsection='true'">1</xsl:when>
	  <xsl:otherwise><xsl:value-of select="$number"/></xsl:otherwise>
	</xsl:choose>
      </xsl:variable>



      <xsl:if test="$proofOnly='false'">
	<h3>Proof Step
    	<xsl:call-template name="numbering">
	  <xsl:with-param name="number" select="$num"/>
    	  <xsl:with-param name="prefix" select="$pref"/>
	</xsl:call-template>
    	</h3>
	
	We consider the <xsl:apply-templates select="complexityInput"/>
	TcT provides the certificate
	<xsl:apply-templates select="complexityInput/answer"/> on above problem.
      </xsl:if>
      <xsl:choose>

	
      	<xsl:when test="proofDetail/transformation">
	  <xsl:choose>
	    <xsl:when test="proofDetail/transformation/progress">
	      <xsl:apply-templates select="proofDetail/transformation">
		<xsl:with-param name="prefix" select="$pref"/>
		<xsl:with-param name="number" select="$num"/>
	      </xsl:apply-templates>
	    </xsl:when>
	    <xsl:otherwise>
	      <xsl:apply-templates select="proofDetail/transformation/subProofs/*">
		<xsl:with-param name="prefix" select="$pref"/>
		<xsl:with-param name="number" select="$num"/>
	      </xsl:apply-templates>		
	    </xsl:otherwise>
	  </xsl:choose>
      	</xsl:when>

	
	<xsl:when test="proofDetail/ite">
	  <xsl:apply-templates select="proofDetail/ite/subProof/proofNode">
	    <xsl:with-param name="prefix" select="$pref"/>
	    <xsl:with-param name="number" select="$num"/>
	  </xsl:apply-templates>
	</xsl:when>


	<xsl:when test="proofDetail/oneOf">
	  <xsl:choose>

	    <!-- success -->
	    <xsl:when test="proofDetail/oneOf/subProof">
	      <xsl:apply-templates select="proofDetail/oneOf/subProof/proofNode">
		<xsl:with-param name="prefix" select="$pref"/>
		<xsl:with-param name="number" select="$num"/>
	      </xsl:apply-templates>
	    </xsl:when>

	    <!-- failure -->
	    <xsl:otherwise>
	      <xsl:for-each select="proofDetail/oneOf/failures">
		Non of the processors succeeded on the problem.
		<div class="indent">
		  <h3>Failed Attempt <xsl:value-of select="$number"/>.<xsl:number/></h3>
		  <xsl:apply-templates select="proofNode">
		    <xsl:with-param name="prefix" select="''"/>
		    <xsl:with-param name="number"><xsl:number/></xsl:with-param>
		  </xsl:apply-templates>
		</div>
	      </xsl:for-each>
	    </xsl:otherwise>
	  </xsl:choose>
	</xsl:when>

	<xsl:when test="proofDetail/order">
	  <xsl:apply-templates select="proofDetail/order"/>
	</xsl:when>

	<xsl:when test="proofDetail/empty">
	  The input problem does not contain any strict rules, the complexity
	  is trivially bounded by O(1).
	</xsl:when>


      	<xsl:when test="proofDetail/proofdata">
	  <pre class="proofDetail/proofdata">
	    <xsl:value-of select="proofDetail/proofdata"></xsl:value-of>
	  </pre>
      	</xsl:when>


      	<xsl:otherwise>
      	  unknown proofDetail node.
      	</xsl:otherwise>

      </xsl:choose>
    </xsl:template>


    <xsl:template match="order">
      <xsl:choose>
	<xsl:when test="incompatible">compatibility cannot be shown</xsl:when>
	<xsl:when test="empty">the problem does not contain rules to orient</xsl:when>
	<xsl:when test="inapplicable"><xsl:value-of select="inapplicable"/></xsl:when>
	<xsl:when test="compatible">
	  The rules are oriented by the following
	  <xsl:apply-templates select="compatible/interpretation"/>
	</xsl:when>
      </xsl:choose>
    </xsl:template>

    <xsl:template match="compose">
      <xsl:param name="number"/>
      <xsl:param name="prefix"/>
      
      We can orient following rules strictly:
      <table>
	<xsl:attribute name="align">center</xsl:attribute>
	<xsl:apply-templates select="rSubProof/proofNode/complexityInput/relation/strictDPs/rules" mode="intable">		
	  <xsl:with-param name="arr">&#8594;</xsl:with-param>
	</xsl:apply-templates>		  
	<xsl:apply-templates select="rSubProof/proofNode/complexityInput/relation/strictTrs/rules" mode="intable">		
	  <xsl:with-param name="arr">&#8594;</xsl:with-param>
	</xsl:apply-templates>	
      </table>

      <div class='indent'>
	<xsl:apply-templates select="rSubProof/proofNode">
	  <xsl:with-param name="prefix" select="$prefix"/>
	  <xsl:with-param name="number" select="$number"/>
	  <xsl:with-param name="proofOnly" select="'false'"/>
	  <xsl:with-param name="subsection" select="'true'"/>
	</xsl:apply-templates>
      </div>
    </xsl:template>


    <xsl:template match="dp">
      We add following dependency 
      <xsl:choose>
	<xsl:when test="pairs">pairs</xsl:when>
	<xsl:when test="tuples">tuples</xsl:when>
      </xsl:choose>
      <table>
	<xsl:attribute name="align">center</xsl:attribute>
	<xsl:apply-templates select="strictDPs/rules" mode="intable">		
	  <xsl:with-param name="arr">&#8594;</xsl:with-param>
	</xsl:apply-templates>		  
	<xsl:apply-templates select="weakDPs/rules" mode="intable">		
	  <xsl:with-param name="arr">&#8594;<sup>=</sup></xsl:with-param>
	</xsl:apply-templates>		  
      </table>
      and adapt the set of starting terms appropriately.
    </xsl:template>


    <xsl:template match="transformation">
      <xsl:param name="prefix"/>
      <xsl:param name="number"/>

      <xsl:call-template name="proofNodeHeader">
	<xsl:with-param name="prefix" select="$prefix"/>
	<xsl:with-param name="number" select="$number"/>
      </xsl:call-template>
      <p>
    	<xsl:apply-templates select="transformationProof/*">
	  <xsl:with-param name="prefix" select="$prefix"/>
	  <xsl:with-param name="number" select="$number"/>
	</xsl:apply-templates>
      </p>
      
      <xsl:choose>

      	<xsl:when test="count(subProofs/proofNode) = 0">
      	  The transformation did not result in further sub-problems.
      	</xsl:when>

      	<xsl:when test="count(subProofs/proofNode) = 1">
	  <xsl:apply-templates select="subProofs/proofNode">
	    <xsl:with-param name="prefix" select="$prefix"/>
	    <xsl:with-param name="number" select="$number + 1"/>
	    <xsl:with-param name="proofOnly" select="'false'"/>
	  </xsl:apply-templates>
      	</xsl:when>

      	<xsl:otherwise>
	  The transformation results in <xsl:value-of select="count(subProofs/proofNode)"/> new problems.
	  Overall TcT provides the certificate
	  <xsl:apply-templates select="complexityInput/answer"/>, 
	  which is obtained obtained by combination of the following proofs.
	  <xsl:variable name="pref">
	    <xsl:call-template name="subsection">
	      <xsl:with-param name="prefix" select="$prefix"/>
	      <xsl:with-param name="number" select="$number"/>
	    </xsl:call-template>
	    .<xsl:number/>
	  </xsl:variable>
	  <xsl:for-each select="subProofs/proofNode">
	    <div class="indent">
	      <xsl:call-template name="proofNodeHeader">
		<xsl:with-param name="prefix"><xsl:value-of select="$pref"/></xsl:with-param>
		<xsl:with-param name="number">1</xsl:with-param>
	      </xsl:call-template>
	      We consider the <xsl:apply-templates select="complexityInput"/>
	      TcT provides the certificate
	      <xsl:apply-templates select="complexityInput/answer"/>.
	      <div class="indent">
		<xsl:apply-templates select=".">
		  <xsl:with-param name="prefix"><xsl:value-of select="$pref"/></xsl:with-param>
		  <xsl:with-param name="number">1</xsl:with-param>
		</xsl:apply-templates>
	      </div>
	    </div>
	  </xsl:for-each>
      	</xsl:otherwise>

      	</xsl:choose>
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
	      <p>
		<table>
	      <xsl:attribute name="align">center</xsl:attribute>
	      <xsl:apply-templates select="strictDPs/rules" mode="intable">		
		<xsl:with-param name="arr">&#8594;</xsl:with-param>
	      </xsl:apply-templates>		  
	      <xsl:apply-templates select="weakDPs/rules" mode="intable">		
		<xsl:with-param name="arr">&#8594;<sup>=</sup></xsl:with-param>
	      </xsl:apply-templates>		  
		</table>
	      </p>
	      <xsl:if test="strictTrs or weakTrs">
		together with the rewrite rules
	      </xsl:if>
	    </xsl:when>
	    <xsl:otherwise>
	  rewrite rules
	    </xsl:otherwise>
	  </xsl:choose>
	  <xsl:if test="strictTrs or weakTrs">
	    <p>
	      <table>
		<xsl:attribute name="align">center</xsl:attribute>
		<xsl:apply-templates select="strictTrs/rules" mode="intable">		
		  <xsl:with-param name="arr">&#8594;</xsl:with-param>
		</xsl:apply-templates>		  
		<xsl:apply-templates select="weakTrs/rules" mode="intable">		
		  <xsl:with-param name="arr">&#8594;<sup>=</sup></xsl:with-param>
		</xsl:apply-templates>		  
	      </table>
	    </p>
	  </xsl:if>
	</xsl:when>
	<xsl:otherwise>
	  empty set of rewrite rules
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>

    <xsl:template match="rules" mode="intable">
        <xsl:param name="arr"/>
	<xsl:for-each select="*">
	      <tr>
		<td align="right">
		  <xsl:apply-templates select="lhs"/>
		</td>
		<td align="center">
		  <xsl:value-of select="$arr"/>
		</td>
		<td align="left">
		  <xsl:apply-templates select="rhs"/>
		</td>
	      </tr>
	    </xsl:for-each>
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


    <!-- misc -->

    <xsl:template name="numbering">
      <xsl:param name="number"/>
      <xsl:param name="prefix"/>
      <xsl:if test="$prefix != ''"><xsl:value-of select="$prefix"/>.</xsl:if><xsl:value-of select="$number"/>
    </xsl:template>

    <xsl:template name="proofNodeHeader">
      <xsl:param name="number"/>
      <xsl:param name="prefix"/>
      <p>
    	<h3>Proof Step
    	<xsl:call-template name="numbering">
	  <xsl:with-param name="number" select="$number"/>
    	  <xsl:with-param name="prefix" select="$prefix"/>
	</xsl:call-template>
    	</h3>
      </p>
    </xsl:template>

    <xsl:template match="subsection">
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
      <xsl:param name="inner">False</xsl:param>
      <xsl:choose>
	<xsl:when test="coefficient">
	  <xsl:apply-templates select="coefficient"/>
	</xsl:when>
	<xsl:when test="variable">
	  <span class="var">
	    x<sub><xsl:value-of select="variable/text()"/></sub>
	  </span>
	</xsl:when>
	<xsl:when test="sum">
	  <xsl:if test="$inner = 'True'">
	    <xsl:text>(</xsl:text>                    
	  </xsl:if>
	  <xsl:for-each select="sum/polynomial">
	    <xsl:apply-templates select="."/>
	    <xsl:if test="position() != last()"> + </xsl:if>                    
	  </xsl:for-each>
	  <xsl:if test="$inner = 'True'">
	    <xsl:text>)</xsl:text>                    
	  </xsl:if>
	</xsl:when>
	<xsl:when test="product">
	  <xsl:for-each select="product/polynomial">
	    <xsl:apply-templates select=".">
	      <xsl:with-param name="inner">True</xsl:with-param>
	    </xsl:apply-templates>
	    <xsl:if test="position() != last()"> &#183; </xsl:if> <!-- cdot -->                    
	  </xsl:for-each>
	</xsl:when>
	<xsl:when test="max">
	  <xsl:text>max(</xsl:text>
	  <xsl:for-each select="max/polynomial">
	    <xsl:apply-templates select="."/>
	    <xsl:if test="position() != last()">,</xsl:if>                    
	  </xsl:for-each>
	  <xsl:text>)</xsl:text>
	</xsl:when>
	<xsl:when test="min">
	  <xsl:text>min(</xsl:text>
	  <xsl:for-each select="min/polynomial">
	    <xsl:apply-templates select="."/>
	    <xsl:if test="position() != last()">,</xsl:if>                    
	  </xsl:for-each>
	  <xsl:text>)</xsl:text>
	</xsl:when>
	<xsl:otherwise>unknown polynomial type</xsl:otherwise>
      </xsl:choose>
      
    </xsl:template>
    
    <xsl:template match="integer">
      <xsl:value-of select="text()"/>
    </xsl:template>
    
    <xsl:template match="rational">
      <xsl:value-of select="numerator/text()"/>
      <xsl:variable name="denom" select="denominator/text()"/>
      <xsl:if test="$denom != 1">
	<xsl:text>/</xsl:text>
	<xsl:value-of select="$denom"/>
      </xsl:if>        
    </xsl:template>    

    <xsl:template match="vector">
        <xsl:choose>
            <xsl:when test="count(coefficient) = 0">()</xsl:when>
            <xsl:otherwise>
                <table vertical-align="middle" style="display:inline; border-left-style:solid; border-left-width:thin; border-right-style: solid; border-right-width:thin; border-color:black; border-top-width:0;">
                    <xsl:for-each select="coefficient">
                        <tr>
                            <td>
                                <xsl:apply-templates select="."/>
                            </td>
                        </tr>
                    </xsl:for-each>
                </table>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>
    
    <xsl:template match="matrix">
        <xsl:choose>
            <xsl:when test="count(vector) = 0">()</xsl:when>
            <xsl:otherwise>
                <table vertical-align="middle" style="display:inline; border-left-style:solid; border-left-width:thin; border-right-style: solid; border-right-width:thin; border-color:black; border-top-width:0;">
                    <xsl:call-template name="matrix2">
                        <xsl:with-param name="width" select="count(vector)"/>
                        <xsl:with-param name="heigth" select="count(vector[1]/coefficient)"/>
                        <xsl:with-param name="h" select="1"/>
                    </xsl:call-template>
                </table>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>
    
    <xsl:template name="matrix2">
      <xsl:param name="heigth"/>
      <xsl:param name="width"/>
      <xsl:param name="h"/>
      <tr>
	<xsl:call-template name="matrix3">
	  <xsl:with-param name="width" select="$width"/>
	  <xsl:with-param name="h" select="$h"/>                
	  <xsl:with-param name="w" select="1"/>                
	</xsl:call-template>
      </tr>
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
      <td>
	<xsl:apply-templates select="vector[$w]/coefficient[$h]"/>
      </td>
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
	  <xsl:text>matrix interpretations of dimension </xsl:text> 
	  <xsl:value-of select="matrixInterpretation/dimension/text()"/>
	  <xsl:text> with strict dimension </xsl:text> 
	  <xsl:value-of select="matrixInterpretation/strictDimension/text()"/>
	  <xsl:text> over </xsl:text>
	  <xsl:apply-templates select="matrixInterpretation/domain"/>            
	</xsl:when>
	<xsl:otherwise>
	  some unknown interpretation type
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>
    
    <xsl:template match="interpretation">
      <xsl:apply-templates select="*[1]"/>
      <p>
      	<table>
      	  <xsl:attribute name="align">center</xsl:attribute>
      	  <xsl:for-each select="interpret">
      	    <tr>
      	      <td><xsl:attribute name="align">right</xsl:attribute>
      	      <xsl:text>[</xsl:text><xsl:apply-templates select="*[1]"/><xsl:call-template name="genVars">
      	      <xsl:with-param name="n" select="arity"/>
      	      </xsl:call-template><xsl:text>]</xsl:text>
      	      </td>
      	      <td><xsl:attribute name="align">center</xsl:attribute> = </td>
      	      <td><xsl:attribute name="align">left</xsl:attribute><xsl:apply-templates select="*[3]"/></td>
      	    </tr>
      	  </xsl:for-each>
      	</table>
      </p>
    </xsl:template>
</xsl:stylesheet>
