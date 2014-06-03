package org.nhindirect.stagent.cert;

import java.io.ByteArrayInputStream;
import java.security.cert.CertificateFactory;
import java.security.cert.X509Certificate;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.TreeMap;
import java.util.Map.Entry;

import javax.naming.Context;
import javax.naming.NamingEnumeration;
import javax.naming.NamingException;
import javax.naming.directory.Attributes;
import javax.naming.directory.InitialDirContext;
import javax.naming.directory.SearchControls;
import javax.naming.directory.SearchResult;

import org.apache.commons.io.IOUtils;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.xbill.DNS.Lookup;
import org.xbill.DNS.Record;
import org.xbill.DNS.SRVRecord;
import org.xbill.DNS.Type;

/**
 * Class for looking up public certificates via LDAP.
 * 
 * @author Greg Gurr
 *
 */
public class LDAPCertificateLookup {	
	private static final Log LOGGER = LogFactory.getFactory().getInstance(LDAPCertificateLookup.class);
	
	/**
	 * Search for a public certificate for the passed in email address via LDAP.
	 * Note: LDAP public certs can be "address bound" or "domain bound". You need to try
	 * 		 both.
	 * 
	 * @param directName
	 * 		Contains the Direct "name" (email address or just domain part of email) for which to lookup a public certificate via LDAP.
	 * @return
	 * 		Returns the public x509 certificates that were discovered.
	 */
	@SuppressWarnings("rawtypes")
	public Collection<X509Certificate> lookupLDAP(String directName) {		
		Collection<X509Certificate> resultLdapCerts = new ArrayList<X509Certificate>();
		
		LOGGER.debug("\nBegin LDAPCertificateLookup.lookupLDAP - directName: '" + directName + "' \n");
		
		if (directName == null) {
			return resultLdapCerts;
		}
		
		String domainName = directName;
		int addressAtSignIndex = directName.indexOf("@");
		
		if (addressAtSignIndex != -1) {
			domainName = directName.substring(addressAtSignIndex + 1);
		}
				
		// Get the DNS SRV records for this Direct address domain. The SRV records will contain connection
		// information to the LDAP server.
		List<SRVRecord> srvRecords = getDnsSrvRecords(domainName);		
		
		if ((srvRecords != null) && (srvRecords.size() > 0)) {					
			for (SRVRecord srvRecord : srvRecords) {
				InitialDirContext context = null;
				
				try {					
					context = connectToLDAP(srvRecord);
					
					// Create the search controls
					SearchControls searchCtls = new SearchControls();
					searchCtls.setSearchScope(SearchControls.SUBTREE_SCOPE);					
					
					NamingEnumeration results = null;
					
					// Search LDAP for certificates
					results = context.search("", "(objectclass=inetOrgPerson)", searchCtls);
					
					if ((results != null) && (results.hasMore())) {
						LOGGER.debug("\nFOUND items from LDAP search, looping to find matching email. \n");
						
						while (results.hasMore()) {
				            SearchResult resultItem = (SearchResult) results.next(); 				            
				            Attributes attrs = resultItem.getAttributes();

				            if ((attrs.get("mail") != null) &&
				            		(attrs.get("mail").get() != null)) {
				            	
								String ldapMailAttrValue = (String) attrs.get("mail").get();				
								LOGGER.debug("\nComparing the ldap mail value: '" + ldapMailAttrValue + "' to target email: '" + directName + "'");
								
				            	if (directName.equalsIgnoreCase(ldapMailAttrValue)) {
				            		LOGGER.debug("\nMATCH FOUND for ldap email attribute. Getting value from the ldap attribute 'userCertificate'");
									
						           	byte[] certBytes = (byte[]) attrs.get("userCertificate").get();            						            	
					            	X509Certificate x509Cert = (X509Certificate) convertLdapCertToX509Cert(certBytes);
					            	
					            	resultLdapCerts.add(x509Cert);									
								}       	             	
							}
						}									
					} else {
						LOGGER.debug("\nDid NOT find any items from LDAP search \n");						
					}				
				} catch (Exception e) {
					LOGGER.error("\nError occurred in getting cert from LDAP. " + e.getMessage());
					e.printStackTrace();					
				} finally {
					if (context != null) {
						try {
							context.close();
						} catch (NamingException e) {
							// no-op
						}
					}
				}				
			}	// for loop
		}// if srv records exist
		
		LOGGER.debug("\nEnd lookupLDAP - directName: '" + directName + "' Number records found: " + resultLdapCerts.size() + "\n");
		
		return resultLdapCerts;
	}	
	
	
	/**
	 * Connect to LDAP as defined in the passed DNS SRV record.
	 * 
	 * @param srvRecord
	 * 		Contains the DNS SRV record for which to connect to LDAP.
	 * @return
	 * @throws NamingException 
	 */
	private InitialDirContext connectToLDAP(SRVRecord srvRecord) throws NamingException {
		InitialDirContext context = null;
		
		if (srvRecord != null) {			
			String ldapTarget = srvRecord.getTarget().toString();
			String ldapPort = new Integer(srvRecord.getPort()).toString();
			
			if (ldapTarget.endsWith(".")) {
				ldapTarget = ldapTarget.substring(0, ldapTarget.length() - 1);
			}	
			
			String ldapProviderUrl = "ldap://" + ldapTarget + ":" + ldapPort;	
			
			LOGGER.debug("\nTrying to connect to LDAP for url: " + ldapProviderUrl + "\n");
			
			// set properties for our connection and provider
			Properties properties = new Properties();
			properties.put(Context.INITIAL_CONTEXT_FACTORY, "com.sun.jndi.ldap.LdapCtxFactory");			  
			properties.put(Context.PROVIDER_URL, ldapProviderUrl);
			properties.put("com.sun.jndi.ldap.read.timeout", "7000");
			
			// set properties for anonymus authentication
			properties.put(Context.SECURITY_AUTHENTICATION, "none");
			
			context = new InitialDirContext(properties);	
			
			LOGGER.debug("\nSuccessfully connected to ldap server \n");					
		} 

		return context;
	}

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
			
			LOGGER.debug("\nSuccessfully converted ldap cert bytes to x509 cert \n");
		}
		catch (Exception e)
		{
			LOGGER.error("\nERROR: Failed to convert ldap certificate bytes to x509." + e.getMessage());
			e.printStackTrace();
		}
		finally
		{
			IOUtils.closeQuietly(inputStream);
		}
		
		return retVal;
	}		
	
	/**
	 * Get the DNS SRV records for the passed in "domain" name.
	 * 
	 * @param domainName
	 * 		Contains the "email" domain name for which to retrieve DNS SRV records.
	 * @return
	 * 		Returns a list of "SRVRecord" objects.
	 */
	private List<SRVRecord> getDnsSrvRecords(String domainName) {
		List<SRVRecord> srvRecords = new ArrayList<SRVRecord>();
		List<SRVRecord> sortedSrvRecords = new ArrayList<SRVRecord>();
		
		if (domainName == null) {
			return srvRecords;
		}		
		
		String query = "_ldap._tcp." + domainName;

		LOGGER.debug("\nLooking for DNS SRV records for domain: '"
				+ domainName + "' using query: '" + query + "'\n");

		try {
			Record[] records = new Lookup(query, Type.SRV).run();

			if ((records != null) && (records.length > 0)) {
				LOGGER.debug("\nFOUND SRV records -  count: " + records.length + "\n");
										
				StringBuilder buf = new StringBuilder();
				for (Record record : records) {
					srvRecords.add((SRVRecord) record);
				}
				
				sortedSrvRecords = sortSrvRecords(srvRecords);
				
				logDebugSrvRecords(sortedSrvRecords);
				
				LOGGER.debug(buf.toString());
			} else {
				LOGGER.debug("\nCould NOT find any SRV records for domain: '" + domainName + "' \n");
			}
		} catch (Exception e) {
			LOGGER.debug("\nError occurred in searching for DNS SRV records. " + e.getMessage());
			e.printStackTrace();			
		}
				
		return sortedSrvRecords;
	}
	
	
	/**
	 * Private class that is used to compare DNS SRV records.
	 * We need to sort them based upon "priority" and then by "weight".
	 */
	private class SrvRecordCompatator implements Comparator<SRVRecord> {
		@Override
		public int compare(SRVRecord o1, SRVRecord o2) {
			if ((o1 == null) && (o2 == null)) {
				return 0;				
			} else if ((o1 != null) && (o2 == null)) {
				return 1;
			} else if ((o1 == null) && (o2 != null)) {
				return -1;
			} else if (o1 == o2) {
				return 0;
			} else {
				// Sort by "priority" first (lowest "value" is highest priority)
				if (o1.getPriority() < o2.getPriority()) {
					return -1;
				} else if (o1.getPriority() > o2.getPriority()) {
					return 1;
				} else {
					// Sort by "weight" if the priorities are the same
					if (o1.getWeight() < o2.getWeight()) {
						return 1;
					} else if (o1.getWeight() > o2.getWeight()) {
						return -1;
					} else {
						return 0;
					}
				}
			}
		}
	}	
	
	/**
	 * Sort the passed in "SRVRecord" objects. The sorting is based first on "priority" and then on "weight".
	 * 
	 * @param srvRecords
	 * 		Contains the list of "SRVRecord" objects to sort.
	 * @return
	 * 		Returns a list of sorted "SRVRecord" objects.
	 */
	@SuppressWarnings("rawtypes")
	private List<SRVRecord> sortSrvRecords(List<SRVRecord> srvRecords) {
		List<SRVRecord> sortedList = new ArrayList<SRVRecord>();
		
		if ((srvRecords != null) && (srvRecords.size() > 0)) {
			SrvRecordCompatator srvRecordComparator = new SrvRecordCompatator();
			TreeMap<SRVRecord, SRVRecord> treeMap = new TreeMap<SRVRecord, SRVRecord>(srvRecordComparator);
					
			for (SRVRecord srvRecord : srvRecords) {
				// Have the treeMap "comparator" sort the records
				treeMap.put(srvRecord, srvRecord);
			}

			Set<Entry<SRVRecord, SRVRecord>> set = treeMap.entrySet();
			Iterator<Entry<SRVRecord, SRVRecord>> i = set.iterator();

			while (i.hasNext()) {
				Map.Entry mapEntry = (Map.Entry) i.next();
				
				sortedList.add((SRVRecord) mapEntry.getValue());
			}
		}
		
		return sortedList;
	}
	
	
	/**
	 * Log debug information about the passed in "SRVRecord" objects.
	 * 
	 * @param srvRecords
	 * 		Contains the "SRVRecord" object for which to log debug information.
	 */
	private void logDebugSrvRecords(List<SRVRecord> srvRecords) {
		StringBuilder buf = new StringBuilder();		
		
		if (srvRecords!= null && srvRecords.size() > 0) {
			for (SRVRecord srvRecord : srvRecords) {
				buf.append("\n*** SRV Record *** \n");
				buf.append("\tName: " + srvRecord.getName() + "\n");
				buf.append("\tPort: " + srvRecord.getPort() + "\n");
				buf.append("\tPriority: " + srvRecord.getPriority() + "\n");
				buf.append("\tWeight: " + srvRecord.getWeight() + "\n");
				buf.append("\tType: " + srvRecord.getType() + "\n");
				buf.append("\tRRsetType: " + srvRecord.getRRsetType() + "\n");
				buf.append("\tTTL: " + srvRecord.getTTL() + "\n");
				buf.append("\tDClass: " + srvRecord.getDClass() + "\n");

				if (srvRecord.getTarget() != null) {
					buf.append("\tTarget: " + srvRecord.getTarget() + "\n");
				} else {
					buf.append("\tTarget: NULL \n");
				}

				if (srvRecord.getAdditionalName() != null) {
					buf.append("\tAdditionalName: " + srvRecord.getAdditionalName() + "\n");						
				} else {
					buf.append("\tAdditionalName: NULL \n");
				}				
			}
		} else {
			buf.append("\nSrvRecord list is NULL or EMPTY \n");
		}				
		
		LOGGER.debug(buf.toString());		
	}
	
	
	
}
