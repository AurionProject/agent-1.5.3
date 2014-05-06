package org.nhindirect.stagent.cert.impl;

import static org.junit.Assert.*;

import java.io.ByteArrayInputStream;
import java.security.cert.Certificate;
import java.security.cert.CertificateFactory;
import java.security.cert.X509Certificate;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import javax.naming.Context;
import javax.naming.NamingEnumeration;
import javax.naming.directory.Attributes;
import javax.naming.directory.InitialDirContext;
import javax.naming.directory.SearchControls;
import javax.naming.directory.SearchResult;

import org.apache.commons.io.IOUtils;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.xbill.DNS.CERTRecord;
import org.xbill.DNS.Lookup;
import org.xbill.DNS.Record;
import org.xbill.DNS.SRVRecord;
import org.xbill.DNS.Type;

import junit.framework.TestCase;

public class MyLdapConnectionQueryTest extends TestCase {
	private final String LDAP_PROVIDER_URL = "ldap://ldap.demo.direct-test.com:10389";
	
	
	private InitialDirContext context = null;
	

	 
	@Before
	protected void setUp() throws Exception {
		super.setUp();
	}

	 
	@After
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (context != null) {
			context.close();
		}		
	}
	
	
	
	@Test
	public void testLdapConnection() throws Exception {
		// set properties for our connection and provider
		Properties properties = new Properties();
		properties.put(Context.INITIAL_CONTEXT_FACTORY, "com.sun.jndi.ldap.LdapCtxFactory");			  
		properties.put(Context.PROVIDER_URL, LDAP_PROVIDER_URL);
		properties.put("com.sun.jndi.ldap.read.timeout", "7000");

		// set properties for anonymus authentication
		properties.put(Context.SECURITY_AUTHENTICATION, "none");

		System.out.println("Connecting to LDAP...");
		InitialDirContext context = new InitialDirContext(properties);		
		
		assertNotNull(context);
						
		// Create the search controls
		SearchControls searchCtls = new SearchControls();

		// Specify the search scope
		searchCtls.setSearchScope(SearchControls.SUBTREE_SCOPE);

		// specify the LDAP search filter, just users
		//String searchFilter = "(&(objectClass=user)( cn=Joe Someone))";

		// Specify the attributes to return
		//String returnedAtts[]={"userCertificate"};
		//searchCtls.setReturningAttributes(returnedAtts);
		
		NamingEnumeration results;
		
		results = context.search("", "(objectclass=inetOrgPerson)", searchCtls);
		SearchResult result = null;
		  			
		assertNotNull(results);
		
		if (results.hasMore()) {
			System.out.println("FOUND items in LDAP!! \n ");
		} else {
			System.out.println("No results returned from LDAP \n");
		}
		
		while (results.hasMore()) {
            SearchResult resultItem = (SearchResult) results.next (); 
            
            Attributes attrs = resultItem.getAttributes();
            System.out.println("\nLdap Result Item:");
            if ((attrs.get("mail") != null) &&
            		(attrs.get("mail").get() != null)) {
            	
				String mailValue = (String) attrs.get("mail").get();				
				System.out.println("\tComparing the ldap value: '" + mailValue + "' to 'dts505@direct2.demo.direct-test.com'...");
				
            	if ("dts505@direct2.demo.direct-test.com".equalsIgnoreCase(mailValue)) {
					System.out.println("\t\t*** SUCCESS: MATCHED The ldap item '" + mailValue + "' to the target email ***");
					
		           	byte[] certBytes = (byte[]) attrs.get("userCertificate").get();            	
	            	
	            	System.out.println("\tExtract cert value byte length: " + certBytes.length);
	            	
	            	StringBuilder buf = new StringBuilder();
	            	for (int i = 0; i < certBytes.length; i++) {
	            		buf.append(certBytes[i]);
					}
	            	System.out.println("\tCert bytes: " + buf.toString());
	            	
	            	
	            	X509Certificate x509Cert = (X509Certificate) convertLdapCertToX509Cert(certBytes);
	            	
	            	assertNotNull(x509Cert);
	            	
	            	
					
				} else {
					System.out.println("\t\tDid NOT match ldap item to target email");
				}         	             	
			}
		}
		
		
		
		
		
		
	}
	
	
	
	@Test
	public void testGetDNS_SRV_Record() throws Exception {
		
		List<SRVRecord> srvRecords = new ArrayList<SRVRecord>();
		String query = "_ldap._tcp.domain2.demo.direct-test.com";
		
		System.out.println("\nQuerying DNS for SRV records with url: '" + query + "'");

		try {
			Record[] records = new Lookup(query, Type.SRV).run();

			if ((records != null) && (records.length > 0)) {
				System.out.println("\nFOUND SRV records!!  count: " + records.length);
										
				StringBuilder buf = new StringBuilder();
				for (Record record : records) {
					SRVRecord srv = (SRVRecord) record;

					srvRecords.add(srv);

					buf.append("\n*** SRV Record *** \n");
					buf.append("\tName: " + srv.getName() + "\n");
					buf.append("\tPort: " + srv.getPort() + "\n");
					buf.append("\tPriority: " + srv.getPriority() + "\n");
					buf.append("\tType: " + srv.getType() + "\n");
					buf.append("\tRRsetType: " + srv.getRRsetType() + "\n");
					buf.append("\tTTL: " + srv.getTTL() + "\n");
					buf.append("\tDClass: " + srv.getDClass() + "\n");
					buf.append("\tWeight: " + srv.getWeight() + "\n");

					if (srv.getTarget() != null) {
						buf.append("\tTarget: " + srv.getTarget() + "\n");
					} else {
						buf.append("\tTarget: NULL \n");
					}

					if (srv.getAdditionalName() != null) {
						buf.append("\tAdditionalName: "
								+ srv.getAdditionalName() + "\n");
					} else {
						buf.append("\tAdditionalName: NULL \n");
					}
				}
				
				System.out.println(buf.toString());
			} else {
				System.out.println("\nCould NOT find any SRV records for: '" + query + "'");
			}
		} catch (Exception e) {
			System.out.println("\nERROR occurred in searching for DNS SRV records. " + e.getMessage());
			e.printStackTrace();			
		}		
		
		
	}
	
	
	
	//-------------------------------------------------------------------------------------------------------------------
	// Private
	//-------------------------------------------------------------------------------------------------------------------	
	
	
	/**
	 * Convert a ldap byte array cert to a x509 certificate.
	 * 
	 * @param ldapCertBytes
	 * 		Contains the certificate byte array we got out of ldap.
	 * @return
	 * 		Returns a X509Certificate object.
	 */
	private X509Certificate convertLdapCertToX509Cert(byte[] ldapCertBytes)
	{
		X509Certificate retVal = null;
		ByteArrayInputStream inputStream = null;

		try
		{
			final CertificateFactory cf = CertificateFactory.getInstance("X.509");
			inputStream = new ByteArrayInputStream(ldapCertBytes);
			retVal = (X509Certificate)cf.generateCertificate(inputStream);
			
			System.out.println("\n*** Successfully converted cert bytes to x509 cert ***");
		}
		catch (Exception e)
		{
			System.out.println("ERROR: Failed to convert certificate from DNS byte data." + e.getMessage());
			e.printStackTrace();
		}
		finally
		{
			IOUtils.closeQuietly(inputStream);
		}
		
		return retVal;
	}
	

	
	

}
