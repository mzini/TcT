<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">
    <xsl:output method="text"/>

    <xsl:template match="/">
      <xsl:choose>
	<!-- ceta  -->
	<xsl:when test="/certificationProblem">
	  <xsl:text>YES(?,</xsl:text>
	  <xsl:apply-templates select="/certificationProblem/complexityInput/*[3]"/>
	  <xsl:text>)</xsl:text>
	</xsl:when>
	<!-- tct -->
	<xsl:when test="/tctOutput">
	  <xsl:apply-templates select="/tctOutput/input/answer"/>
	</xsl:when>


	<xsl:otherwise>
	  <xsl:text>ERROR</xsl:text>
	</xsl:otherwise>
      </xsl:choose>
    </xsl:template>


    <xsl:template match="answer">
      <xsl:choose>
	<xsl:when test="no"><span class="no">NO</span></xsl:when>
	<xsl:when test="maybe"><span class="maybe">MAYBE</span></xsl:when>
	<xsl:when test="timeout"><span class="timeout">TIMEOUT</span></xsl:when>
	<xsl:when test="certified">
	  <xsl:text>YES(</xsl:text>	  
	  <xsl:apply-templates select="certified/lowerbound"/>
	  <xsl:text>,</xsl:text>	  
	    <xsl:apply-templates select="certified/upperbound"/>
	  <xsl:text>)</xsl:text>	  
	</xsl:when>
      </xsl:choose>
    </xsl:template>

    <xsl:template match="polynomial">
       <xsl:choose>
            <xsl:when test="text() = 0">O(1)</xsl:when>
            <xsl:otherwise>
	      <xsl:text>O(n^</xsl:text><xsl:value-of select="text()"/><xsl:text>)</xsl:text>
	    </xsl:otherwise>
        </xsl:choose>        
    </xsl:template>

    <xsl:template match="unknown">
      <xsl:text>?</xsl:text>
    </xsl:template>

</xsl:stylesheet>
