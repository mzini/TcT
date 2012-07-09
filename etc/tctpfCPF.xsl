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
   <certificationProblem>
     <xsl:attribute name="xsi:noNamespaceSchemaLocation">cpf.xsd</xsl:attribute>
     <xsl:apply-templates select="input"/>

     <cpfVersion>2.1</cpfVersion>

     <proof>
       <xsl:apply-templates select="proofNode"/>
     </proof>

     <origin>
       <proofOrigin>
	 <tool>
	   <name>TcT</name>
	   <version><xsl:value-of select="version"/></version>
	 </tool>
       </proofOrigin>
     </origin>
   </certificationProblem>      
 </xsl:template>


 <xsl:template match="input">
   <input>
     <complexityInput>
       <trsInput>
	 <xsl:copy-of select="trs"/>
	 <xsl:if test="strategy/innermost">
	   <strategy><innermost/></strategy>
	 </xsl:if>
	 <xsl:if test="count(relativeRules/rules/*) > 0">
	   <xsl:copy-of select="relativeRules"/>
	 </xsl:if>
	 </trsInput>
	 <xsl:copy-of select="complexityMeasure/*"/>
	 <xsl:copy-of select="answer/certified/upperbound/*"/>
       </complexityInput>
     </input>
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
	<complexityProof><rIsEmpty/></complexityProof>
      </xsl:when>

      <xsl:when test="proofDetails/order/compatible">
	<complexityProof>
	  <ruleShifting>
	    <orderingConstraintProof>
	      <redPair>
		<xsl:apply-templates select="order/compatible" mode="inCompose"/>
	      </redPair>
	    </orderingConstraintProof>
	    
	    <trs>
	      <xsl:copy-of select="complexityInput/relation/strictTrs/rules"/>
	    </trs>

	    <complexityProof>
	      <rIsEmpty/>
	    </complexityProof>
	  </ruleShifting>
	</complexityProof>
		
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
		<complexityProof>
		  <ruleShifting>
		    <orderingConstraintProof>
		      <redPair>
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
		      </redPair>
		    </orderingConstraintProof>
		    
		    <trs>
		      <xsl:copy-of select="transformationProof/compose/rSubProof/proofNode/complexityInput/relation/strictTrs/rules"/>
		    </trs>

		    <xsl:apply-templates select="subProofs/proofNode"/>
		  </ruleShifting>
		</complexityProof>
	      </xsl:when>	      
	      <xsl:otherwise>
		<xsl:call-template name="notCPF">
		  <xsl:with-param name="reason">compose type not addition</xsl:with-param>
		</xsl:call-template>
	      </xsl:otherwise>
	    </xsl:choose>
	  </xsl:when>

	  <xsl:when test="transformationProof/irr">
	    <complexityProof>
	      <removeNonApplicableRules>
		<trs>
		  <rules>
		    <xsl:copy-of select="transformationProof/irr/removal/removed/rule"/>
		  </rules>
		</trs>
		<xsl:apply-templates select="subProofs/proofNode"/>
	      </removeNonApplicableRules>
	    </complexityProof>
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
    <interpretation>
      <xsl:apply-templates select="interpretation/type"/>
      <xsl:copy-of select="interpretation/interpret"/>
    </interpretation>
  </xsl:template>

  <xsl:template match="type">
    <type>
      <xsl:choose>

	<xsl:when test="matrixInterpretation">
	  <matrixInterpretation>
	    <xsl:copy-of select="matrixInterpretation/domain"/>
	    <xsl:copy-of select="matrixInterpretation/dimension"/>
	    <xsl:copy-of select="matrixInterpretation/strictDimension"/>
	  </matrixInterpretation>
	</xsl:when>

	<xsl:when test="polynomialInterpretation">
	  <polynomial>
	    <xsl:copy-of select="polynomialInterpretation/domain"/>
	    <xsl:copy-of select="polynomialInterpretation/degree"/>
	  </polynomial>
	</xsl:when>

	<xsl:otherwise>
	  <xsl:call-template name="notCPF">
	    <xsl:with-param name="reason">unsupported interpretation type</xsl:with-param>
	  </xsl:call-template>
	</xsl:otherwise>
      </xsl:choose>
    </type>
  </xsl:template>
</xsl:stylesheet>
