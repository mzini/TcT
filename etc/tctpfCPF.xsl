<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" 
		xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
		exclude-result-prefixes="xsi"
		version="1.0">
  <xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"/>
  <xsl:strip-space elements="*"/>

 <xsl:template name="notCPF">
   <xsl:param name="reason">unknown</xsl:param>
   <xsl:element name="notInCpfFormat">
     <xsl:element name="reason"><xsl:value-of select="$reason"/></xsl:element>
     <xsl:element name="node"><xsl:copy-of select="*"/></xsl:element>
   </xsl:element>
 </xsl:template>
 
  <xsl:template match="/tctOutput">
    <!-- <xsl:processing-instruction name="xml-stylesheet"> -->
    <!--   href="cpfHTML.xsl" type="text/xsl" -->
    <!-- </xsl:processing-instruction> -->

    <xsl:element name="certificationProblem">
      <xsl:attribute name="xsi:noNamespaceSchemaLocation">cpf.xsd</xsl:attribute>

      <input>
	<xsl:apply-templates select="proofNode/complexityInput"/>
      </input>

      <cpfVersion>2.1</cpfVersion>

      <xsl:element name="proof">
	<xsl:apply-templates select="proofNode"/>
      </xsl:element>

      <xsl:element name="origin">
	<xsl:element name="proofOrigin">
	  <xsl:element name="tool">
	    <xsl:element name="name">TCT</xsl:element>
	    <xsl:element name="version"><xsl:value-of select="version"/></xsl:element>
	  </xsl:element>
	</xsl:element>
      </xsl:element>
    </xsl:element>      
  </xsl:template>

  <xsl:template match="complexityInput">
    <xsl:element name="complexityInput">
      <xsl:element name="trsInput">
	<xsl:element name="trs">
	  <xsl:copy-of select="relation/strictTrs/rules"/>
	</xsl:element>
	<xsl:copy-of select="strategy"/>
	<xsl:if test="relation/weakTrs/rules">
	  <xsl:element name="relativeRules">
	    <xsl:copy-of select="relation/weakTrs/rules"/>
	  </xsl:element>
	</xsl:if>
      </xsl:element>
      <xsl:copy-of select="complexityMeasure/*"/>
      <xsl:copy-of select="answer/certified/upperbound/*"/>
    </xsl:element>
  </xsl:template>


  <!-- proofs  -->
  <xsl:template match="proofNode">
    <xsl:choose>
      <xsl:when test="proofDetail/oneOf">
	<xsl:apply-templates select="proofDetail/oneOf/subProof/proofNode"/>
      </xsl:when>

      <xsl:when test="proofDetail/ite">
	<xsl:apply-templates select="proofDetail/ite/subProof/proofNode"/>
      </xsl:when>

      <xsl:when test="proofDetail/empty">
	<xsl:element name="complexityProof">
	  <xsl:element name="rIsEmpty"/>
	</xsl:element>
      </xsl:when>

      <xsl:when test="proofDetails/order/compatible">
	<xsl:element name="complexityProof">
	  <xsl:element name="ruleShifting">
	    <xsl:element name="orderingConstraintProof">
	      <xsl:element name="redPair">
		<xsl:apply-templates select="order/compatible" mode="inCompose"/>
	      </xsl:element>
	    </xsl:element>
	    
	    <xsl:element name="trs">
	      <xsl:copy-of select="complexityInput/relation/strictTrs/rules"/>
	    </xsl:element>

	    <xsl:element name="complexityProof">
	      <xsl:element name="rIsEmpty"/>
	    </xsl:element>
	  </xsl:element>
	</xsl:element>
		
      </xsl:when>
      <xsl:when test="proofDetail/transformation">
	<xsl:apply-templates select="proofDetail/transformation"/>
      </xsl:when>

      <xsl:otherwise>
	<xsl:call-template name="notCPF">
	  <xsl:with-param name="reason">unknown proofDetail element</xsl:with-param>
	</xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template match="transformation">
    <xsl:choose>
      <xsl:when test="progress">
	<xsl:choose>

	  <xsl:when test="transformationProof/compose">
	    <xsl:choose>
	      <xsl:when test="transformationProof/compose/composeBy = 'addition'">
		<xsl:element name="complexityProof">
		  <xsl:element name="ruleShifting">
		    <xsl:element name="orderingConstraintProof">
		      <xsl:element name="redPair">
			<xsl:choose>
			  <xsl:when test="transformationProof/compose/rSubProof/proofNode/proofDetail/order/compatible">
			    <xsl:apply-templates select="transformationProof/compose/rSubProof/proofNode/proofDetail/order/compatible" mode="inCompose"/>
			  </xsl:when>
			  <xsl:otherwise>
			    <xsl:call-template name="notCPF">
			      <xsl:with-param name="reason">compose incompatible order</xsl:with-param>
			    </xsl:call-template>
			  </xsl:otherwise>
			</xsl:choose>
		      </xsl:element>
		    </xsl:element>
		    
		    <xsl:element name="trs">
		      <xsl:copy-of select="transformationProof/compose/rSubProof/proofNode/complexityInput/relation/strictTrs/rules"/>
		    </xsl:element>

		    <!-- <xsl:choose> -->
		    <!--   <xsl:when test="count(subProofs) = 1"> -->
		    <xsl:apply-templates select="subProofs/proofNode"/>
		    <!--   </xsl:when> -->
		    <!--   <xsl:otherwise> -->
		    <!-- 	<xsl:element name="complexityProof"> -->
		    <!-- 	  <xsl:element name="rIsEmpty"/> -->
		    <!-- 	</xsl:element> -->
		    <!--   </xsl:otherwise> -->
		    <!-- </xsl:choose> -->
		  </xsl:element>
		</xsl:element>
	      </xsl:when>
	      <xsl:otherwise>
		<xsl:call-template name="notCPF">
		  <xsl:with-param name="reason">compose type not addition</xsl:with-param>
		</xsl:call-template>
	      </xsl:otherwise>
	    </xsl:choose>
	  </xsl:when>

	  <xsl:otherwise>
	    <xsl:call-template name="notCPF">
	      <xsl:with-param name="reason">unsupported transformation</xsl:with-param>
	    </xsl:call-template>
	  </xsl:otherwise>

	</xsl:choose>
      </xsl:when>

      <xsl:otherwise>
	<xsl:apply-templates select="subProofs/*"/>
      </xsl:otherwise>

    </xsl:choose>
  </xsl:template>


  <!-- helpers -->

  <xsl:template match="compatible" mode="inCompose">
    <xsl:element name="interpretation">
      <xsl:apply-templates select="interpretation/type"/>
      <xsl:copy-of select="interpretation/interpret"/>
    </xsl:element>
  </xsl:template>

  <xsl:template match="type">
    <xsl:element name="type">
      <xsl:choose>

	<xsl:when test="matrixInterpretation">
	  <xsl:element name="matrixInterpretation">
	    <xsl:copy-of select="matrixInterpretation/domain"/>
	    <xsl:copy-of select="matrixInterpretation/dimension"/>
	    <xsl:copy-of select="matrixInterpretation/strictDimension"/>
	  </xsl:element>
	</xsl:when>

	<xsl:when test="polynomialInterpretation">
	  <xsl:element name="polynomial">
	    <xsl:copy-of select="polynomialInterpretation/domain"/>
	    <xsl:copy-of select="polynomialInterpretation/degree"/>
	  </xsl:element>
	</xsl:when>

	<xsl:otherwise>
	  <xsl:call-template name="notCPF">
	    <xsl:with-param name="reason">unsupported interpretation type</xsl:with-param>
	  </xsl:call-template>
	</xsl:otherwise>
      </xsl:choose>
    </xsl:element>
  </xsl:template>
</xsl:stylesheet>
