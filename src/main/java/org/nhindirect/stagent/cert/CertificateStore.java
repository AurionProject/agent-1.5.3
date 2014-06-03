/* 
Copyright (c) 2010, NHIN Direct Project
All rights reserved.

Authors:
   Umesh Madan     umeshma@microsoft.com
   Greg Meyer      gm2552@cerner.com
 
Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer 
in the documentation and/or other materials provided with the distribution.  Neither the name of the The NHIN Direct Project (nhindirect.org). 
nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, 
THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS 
BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE 
GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, 
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF 
THE POSSIBILITY OF SUCH DAMAGE.
*/

package org.nhindirect.stagent.cert;

import java.security.cert.X509Certificate;
import java.util.ArrayList;
import java.util.Collection;
import java.util.GregorianCalendar;
import java.util.Iterator;

import javax.mail.internet.InternetAddress;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.nhindirect.stagent.CryptoExtensions;
import org.nhindirect.stagent.cert.impl.CRLRevocationManager;
import org.nhindirect.stagent.cert.impl.DNSCertificateStore;

/**
 * Abstract base class for a certificate store implementation.  It does not implement any specific certificate storage functions
 * against a certificate repository implementation.  Storage specific implementation should over ride this class to communicate
 * with the underlying storage medium.
 * @author Greg Meyer
 * @author Umesh Madan
 *
 */
public abstract class CertificateStore implements X509Store, CertificateResolver
{	
	private static final Log LOGGER = LogFactory.getFactory().getInstance(CertificateStore.class);
	
	/**
	 * {@inheritDoc}
	 */
    public abstract boolean contains(X509Certificate cert);

	/**
	 * {@inheritDoc}
	 */    
    public abstract void add(X509Certificate cert);

	/**
	 * {@inheritDoc}
	 */    
    public abstract void remove(X509Certificate cert);

	/**
	 * {@inheritDoc}
	 */    
    public Collection<X509Certificate> getCertificates(String subjectName)
    {
		LOGGER.debug("\nBegin CertificateStore.getCertificates (String) - " + subjectName + " \n");
		
        Collection<X509Certificate> retVal = new ArrayList<X509Certificate>();

        Collection<X509Certificate> certs = getAllCertificates();

        if (certs == null)
            return retVal;

        for (X509Certificate cert : certs) 
        {
            if (CryptoExtensions.certSubjectContainsName(cert, subjectName)) 
            {
                retVal.add(cert);
            } 
        }

        return retVal;
    }
	/**
	 * {@inheritDoc}
	 */    
    public void add(Collection<X509Certificate> certs)
    {
        if (certs == null)
        {
            throw new IllegalArgumentException();
        }

        for (X509Certificate cert : certs)
        {
            add(cert);
        }
    }
    
	/**
	 * {@inheritDoc}
	 */    
    public void remove(Collection<X509Certificate> certs)
    {
        if (certs == null)
        {
            throw new IllegalArgumentException();
        }
        
        for (X509Certificate cert : certs)
        {
            remove(cert);
        }
    }
    
	/**
	 * {@inheritDoc}
	 */    
    public void remove(String subjectName)
    {
    	Collection<X509Certificate> certs = getCertificates(subjectName);
        if (certs != null && certs.size() > 0)
        {
            remove(certs);
        }
    }
    
	/**
	 * {@inheritDoc}
	 */    
    public void update(X509Certificate cert)
    {

    	try
    	{
	        if (contains(cert))
	        {
	            remove(cert);
	        }
	        add(cert);
    	}
    	catch (Exception e)
    	{
    		LOGGER.warn("Exception attempting to update cert in certificate store: " + e.getMessage());
    	}
    }
    
	/**
	 * {@inheritDoc}
	 */    
    public void update(Collection<X509Certificate> certs)
    {
        if (certs == null)
        {
            throw new IllegalArgumentException();
        }
        
        for (X509Certificate cert : certs)
        {
            update(cert);
        }
    }    
    
	/**
	 * {@inheritDoc}
	 */    
    public abstract Collection<X509Certificate> getAllCertificates();    
    
	
	/**
	 * {@inheritDoc}
	 */	
	public Collection<X509Certificate> getCertificates(InternetAddress address)
    {
		if (address != null) {
			LOGGER.debug("\nBegin CertificateStore.getCertificates (InternetAddress) - " + address.getAddress() + " \n");			
		} else {
			LOGGER.debug("\nBegin CertificateStore.getCertificates (InternetAddress) - NULL \n");
		}
		
        return getUsableCerts(address);
    }
	
    protected Collection<X509Certificate> getUsableCerts(InternetAddress address)
    {
    	LOGGER.debug("\nBegin CertificateStore.getUsableCerts - Address: '" + address + "' \n");
    	
        if (address == null)
        {
            throw new IllegalArgumentException();
        }

        // may need to do some parsing of the address because the some email clients may send real name information along with the address
        int index = 0;
        String theAddress = address.getAddress();
        if ((index = theAddress.indexOf("<")) > -1 && theAddress.endsWith(">"))
        {
        	theAddress = theAddress.substring(index + 1);
       		theAddress = theAddress.substring(0, theAddress.length() - 1);
        }
        
        // search for "+" extension on the email address
        if (theAddress.indexOf("+") > -1 && theAddress.indexOf("@") > -1)
        {
        	int startIndex = theAddress.indexOf("+");
        	int endIndex = theAddress.indexOf("@");
        	
        	theAddress = theAddress.substring(0, startIndex) + theAddress.substring(endIndex);
        }
        
        LOGGER.debug("\nIn CertificateStore.getUsableCerts - about to call 'getCertificates' with String param '" + 
        		"EMAILADDRESS=" + theAddress + "'\n");
        
        // NOTE: This calls child class (DNSCertificateStore, KeyStoreCertificateStore etc.) "getCertificates" method
        Collection<X509Certificate> certs = getCertificates("EMAILADDRESS=" + theAddress);
        
        if (certs == null || certs.size() == 0)
        {
        	// find by host       	
        	if ((index = theAddress.indexOf("@")) > -1)
        	{
        		String theDomain = theAddress.substring(index + 1);
        		
                LOGGER.debug("\nIn CertificateStore.getUsableCerts - Did NOT find any address bound certs, about to call 'getCertificates' with String param '" + 
                		"EMAILADDRESS=" + theDomain + "'\n");
                
                // NOTE: This calls child class (DNSCertificateStore, KeyStoreCertificateStore etc.) "getCertificates" method
        		certs = getCertificates("EMAILADDRESS=" + theDomain);
        		
        		if ((certs == null) || (certs.size() == 0)) {
        			// We only want to search LDAP if we just finished a DNS search
        			if (this instanceof DNSCertificateStore) {        				
               			LOGGER.debug("\nIn CertificateStore.getUsableCerts - Could not find certs via DNS, trying LDAP \n"); 
            			certs = lookupCertsViaLDAP(theAddress);
					}
				}
        	}
        } 
        
        LOGGER.debug("\nEnd CertificateStore.getUsableCerts - Address: '" + address + "' about to call 'filterUsable(certs)' \n");

        return filterUsable(certs);
    }
        
    /**
     * Look up public certs via LDAP for the passed in Direct address.
     * 
     * @param theAddress
     * 		Contains the direct address for which to lookup certs.
     * @return
     * 		Returns a collection of X509 certs.
     */
    private Collection<X509Certificate> lookupCertsViaLDAP(String theAddress) {
    	Collection<X509Certificate> certs = new ArrayList<X509Certificate>();
    	
    	LOGGER.debug("\nBegin CertificateStore.lookupCertsViaLDAP ");
    	
    	if (theAddress != null && theAddress.length() > 0) {
    		int indexAtSign = theAddress.indexOf("@");
    	   	String theDomain = theAddress;

    	   	if (indexAtSign > -1) {
    	   		theDomain = theAddress.substring(indexAtSign + 1);
			}
    		
    	   	LDAPCertificateLookup ldapCertLookup = new LDAPCertificateLookup();
    	   	
    	   	// First lookup certs in LDAP for the direct "address"
    	   	certs = ldapCertLookup.lookupLDAP(theAddress);
    	   	
    	   	if ((certs == null) || (certs.size() == 0)) {
    	   		if (indexAtSign != -1) {
    	   			// Second lookup certs in LDAP for the direct "domain"
    	   			certs = ldapCertLookup.lookupLDAP(theDomain);
				}   	   		
			}
		}

    	LOGGER.debug("\nEnd CertificateStore.lookupCertsViaLDAP ");
    	
		return certs;
	}

	/*
     * Removed certs that are not valid due to date expiration, CLR lists, or other revocation criteria
     */
    protected Collection<X509Certificate> filterUsable(Collection<X509Certificate> certs)
    {
    	Collection<X509Certificate> filteredCerts = new ArrayList<X509Certificate>();
    	
    	logX509CertData(certs, "\nBegin CertificateStore.filterUsable - Input cert data collection: \n");
    	
        for (X509Certificate cert : certs)
        {
        	try
        	{
                /*
                 * flow control based on exception handling is generally bad
                 * practice, but this is how the X509Certificate checks validity
                 * based on date (instead of returning a boolean)
                 */
        		cert.checkValidity(new GregorianCalendar().getTime());
        		
        		// Search CRLs to determine if this certificate has been revoked
        		RevocationManager revocationManager = CRLRevocationManager.getInstance();
        		if (!revocationManager.isRevoked(cert))
                    filteredCerts.add(cert);
        	} 
            catch (Exception e) 
            {
            	LOGGER.warn("filterUsable(Collection<X509Certificate> certs) - Certificate with DN " + cert.getSubjectDN() + " is not valid.", e);
            }
        }
        
    	logX509CertData(filteredCerts, "\nEnd CertificateStore.filterUsable - Filtered cert data collection: \n");
        
        return filteredCerts.size() == 0 ? null : filteredCerts;
    }

	/**
	 * Log debug information about the passed in X509 cert data.
	 * 
	 * @param certs
	 * 		Contains the collection of cert data to log.
	 * @param titleText
	 * 		Contains the title text to log.
	 */
	@SuppressWarnings("rawtypes")
	private void logX509CertData(Collection<X509Certificate> certs, String titleText) {
		StringBuilder buf = new StringBuilder(titleText); 
		
		if ((certs != null) && (certs.size() > 0)) {
			for (Iterator iterator = certs.iterator(); iterator.hasNext();) {			
				X509Certificate x509Cert = (X509Certificate) iterator.next();
					
				buf.append("\tCert \n");
				buf.append("\t\tType: " + x509Cert.getType() + "\n");
				
				if (x509Cert.getSubjectDN() != null) {
					buf.append("\t\tSubjectDN: " + x509Cert.getSubjectDN().getName() + "\n");
				} else {
					buf.append("\t\tSubjectDN: NULL \n");
				}
				
				if (x509Cert.getIssuerDN() != null) {
					buf.append("\t\tIssuerDN: " + x509Cert.getIssuerDN().getName() + "\n");
				} else {
					buf.append("\t\tIssuerDN: NULL \n");
				}																			
			}   			
		} else {
			buf.append("\tCert collection is NULL or emtpy \n");
		}
		
		LOGGER.debug(buf.toString());			
	}
    
    
    
    

}
