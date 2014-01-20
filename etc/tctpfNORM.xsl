<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                xmlns:exsl="http://exslt.org/common"
                extension-element-prefixes="exsl"
                version="1.0">
  
    <xsl:template match="proofNode" mode="filter">
      <xsl:choose>

	<xsl:when test="proofDetail/proofNode">
	  <xsl:apply-templates select="proofDetail/proofNode" mode="filter"/>
	</xsl:when>
      	<xsl:when test="proofDetail/ite">
      	  <xsl:apply-templates select="proofDetail/ite/subProof/proofNode" mode="filter"/>
      	</xsl:when>
	
	<xsl:when test="proofDetail/timeout">
	  <xsl:variable name="p">
	    <proofNode>
	      <xsl:copy-of select="complexityInput"/>
	      <xsl:copy-of select="processor"/>
	      <proofDetail>
		<xsl:copy-of select="proofDetail/timeout/subProof/*"/>
	      </proofDetail>
	    </proofNode>
	  </xsl:variable>
      	  <xsl:apply-templates select="exsl:node-set($p)" mode="filter"/>	  
	</xsl:when>
	
	<xsl:when test="proofDetail/oneOf/subProof">
      	  <xsl:apply-templates select="proofDetail/oneOf/subProof/proofNode" mode="filter"/>	  
	</xsl:when>
	<xsl:when test="proofDetail/transformation/noprogress">
	  <xsl:apply-templates select="proofDetail/transformation/subProofs/proofNode" mode="filter"/>
	</xsl:when>
      	<xsl:otherwise>
          <xsl:copy>
            <xsl:apply-templates select="@*|node()" mode="filter"/>
          </xsl:copy>
      	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>

    <xsl:template match="@*|node()" mode="filter">
      <xsl:copy>
	<xsl:apply-templates  select="@*|node()" mode="filter"/>
      </xsl:copy>
    </xsl:template>

    <xsl:template match="/tctOutput">
      <xsl:apply-templates select="/tctOutput" mode="filter"/>
    </xsl:template>
</xsl:stylesheet>
