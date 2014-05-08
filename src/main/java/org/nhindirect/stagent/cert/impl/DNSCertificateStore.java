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

package org.nhindirect.stagent.cert.impl;

import java.io.ByteArrayInputStream;
import java.net.UnknownHostException;
import java.security.cert.Certificate;
import java.security.cert.CertificateFactory;
import java.security.cert.X509Certificate;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;
import java.util.TreeMap;

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
import org.apache.jcs.JCS;
import org.apache.jcs.access.exception.CacheException;
import org.apache.jcs.engine.behavior.ICompositeCacheAttributes;
import org.apache.jcs.engine.behavior.IElementAttributes;
import org.nhindirect.stagent.NHINDException;
import org.nhindirect.stagent.cert.CacheableCertStore;
import org.nhindirect.stagent.cert.CertCacheFactory;
import org.nhindirect.stagent.cert.CertStoreCachePolicy;
import org.nhindirect.stagent.cert.CertificateStore;
import org.nhindirect.stagent.cert.impl.annotation.DNSCertStoreBootstrap;
import org.nhindirect.stagent.cert.impl.annotation.DNSCertStoreCachePolicy;
import org.nhindirect.stagent.cert.impl.annotation.DNSCertStoreServers;
import org.nhindirect.stagent.options.OptionsManager;
import org.nhindirect.stagent.options.OptionsParameter;
import org.xbill.DNS.CERTRecord;
import org.xbill.DNS.CNAMERecord;
import org.xbill.DNS.Cache;
import org.xbill.DNS.DClass;
import org.xbill.DNS.ExtendedResolver;
import org.xbill.DNS.Lookup;
import org.xbill.DNS.NSRecord;
import org.xbill.DNS.Name;
import org.xbill.DNS.Record;
import org.xbill.DNS.ResolverConfig;
import org.xbill.DNS.SRVRecord;
import org.xbill.DNS.Type;

import com.google.inject.Inject;
import com.google.inject.internal.Nullable;

/**
 * Certificate store backed by DNS CERT records (RFC 4398) for dynamic lookup and a configurable local cache of off line lookup. 
 * By default the service uses the local node's DNS server configuration for initial DNS queries and a key store implementation for 
 * off line lookups.  The default key store creates new file named NHINDKeyStore with a default file and private key password if the 
 * file does not already exist.
 * <br>
 * Depending the OS TCP implementation, lookups may be cached in native DNS resolvers resulting in optimized lookups.  
 * However this may not always in line with HIPS policies.  Refer to you OS DNS implementation for more details.
 * <br>
 * This service caches DNS entries independently of OS resolver.  Caching can be tuned using the {@link CacheableCertStore} interface.
 * By default, the time to live of a subjects DNS certs is one day and the maximum number of entries is 1000 before the cache
 * is pruned to make room for new entries.  Pruning by default uses a least recently used algorithm.
 * 
 * @author Greg Meyer
 *
 */
public class DNSCertificateStore extends CertificateStore implements CacheableCertStore
{
	private static final String CACHE_NAME = "DNS_REMOTE_CERT_CACHE";
	
	protected static final int DEFAULT_DNS_TIMEOUT = 3; // 3 seconds
	protected static final int DEFAULT_DNS_RETRIES = 2;
	protected static final boolean DEFAULT_DNS_USE_TCP = true;
	
	protected static final int DEFAULT_DNS_MAX_CAHCE_ITEMS = 1000;
	protected static final int DEFAULT_DNS_TTL = 3600; // 1 hour
	
	protected CertificateStore localStoreDelegate;
	protected List<String> servers = new ArrayList<String>();
	protected JCS cache;
	protected CertStoreCachePolicy cachePolicy;

	protected int timeout;
	protected int retries;
	protected boolean useTCP;
	
	private static final Log LOGGER = LogFactory.getFactory().getInstance(DNSCertificateStore.class);
	static 
	{
		Cache ch = Lookup.getDefaultCache(DClass.IN);
		ch.clearCache();
	}
	
	/**
	 * Constructs a service using the machines local DNS server configuration and a default key store implementation for
	 * local lookups.
	 */
	public DNSCertificateStore()
	{
		getServerQuerySettings();
		setServers(null);		
		
		// no longer create a default local
		// bootstrap store by default
		
		// create the in memory cache
		createCache();
	}
	
	
	
	/**
	 * Constructs a service using the server list for DNS lookups and a default key store implementation for
	 * local lookups.
	 * @param servers The DNS users to use for initial certificate resolution.
	 */
	public DNSCertificateStore(Collection<String> servers)
	{
		getServerQuerySettings();
		setServers(servers);
		// no longer create a default local
		// bootstrap store by default
		
		// create the in memory cache
		createCache();
	}
	
	/**
	 * Constructs a service using the server list for DNS lookups and a key store implementation for
	 * local lookups.
	 * @param servers The DNS users to use for initial certificate resolution.
	 * @param localStoreDelegate The certificate store used for local lookups.  This store is also the boot strap store.
	 * The boot strap store may be null.
	 */
	@Inject 
	public DNSCertificateStore(@DNSCertStoreServers Collection<String> servers, 
			@Nullable @DNSCertStoreBootstrap CertificateStore bootstrapStore, @DNSCertStoreCachePolicy CertStoreCachePolicy policy)
	{
		// null boot strap store is OK
		
		getServerQuerySettings();
		setServers(servers);
		
		this.cachePolicy = policy;			
		this.localStoreDelegate = bootstrapStore;	
		
		// create the in memory cache
		createCache();
		
		// no longer create a default local
		// bootstrap store by default if the boot strap is null
		if (localStoreDelegate != null)
			loadBootStrap();
	}	
		
	private void getServerQuerySettings()
	{
		OptionsParameter param = OptionsManager.getInstance().getParameter(OptionsParameter.DNS_CERT_RESOLVER_TIMEOUT);
		timeout = OptionsParameter.getParamValueAsInteger(param, DEFAULT_DNS_TIMEOUT);
		
		param = OptionsManager.getInstance().getParameter(OptionsParameter.DNS_CERT_RESOLVER_RETRIES);
		retries = OptionsParameter.getParamValueAsInteger(param, DEFAULT_DNS_RETRIES);
		
		param = OptionsManager.getInstance().getParameter(OptionsParameter.DNS_CERT_RESOLVER_USE_TCP);
		useTCP = OptionsParameter.getParamValueAsBoolean(param, DEFAULT_DNS_USE_TCP);
	}
	
	private synchronized JCS getCache()
	{
		if (cache == null)
			createCache();
		
		return cache;
	}
	
	private void createCache()
	{
		try
		{
			// create instance
			cache = CertCacheFactory.getInstance().getCertCache(CACHE_NAME, cachePolicy == null ? getDefaultPolicy() : cachePolicy);	
			if (cachePolicy == null)
				cachePolicy = getDefaultPolicy();
		}
		///CLOVER:OFF
		catch (CacheException e)
		{
			LOGGER.warn("DNSCertificateStore - Could not create certificate cache " + CACHE_NAME, e);
		}
		///CLOVER:ON
	}
	
	private CertStoreCachePolicy getDefaultPolicy()
	{
		return new DefaultDNSCachePolicy();
	}
	
	/**
	 * Sets the DNS servers used for initial certificate lookups.  This replaces all currently set DNS server configuration.  This method is thread safe and
	 * may block if a current lookup is currently in progress.
	 * @param servers The DNS servers used for initial certificate lookups.
	 */
	public void setServers(Collection<String> servers)
	{
		if (servers == null || servers.size() == 0)
		{
			String[] configedServers = ResolverConfig.getCurrentConfig().servers();
			
			if (configedServers != null)
			{
				this.servers.addAll(Arrays.asList(configedServers));
			}		
		}		
		else
		{
			this.servers.clear();
			this.servers.addAll(servers);
		}
	}
	
	/**
	 * {@inheritDoc}
	 */
    public boolean contains(X509Certificate cert)
    {
    	return localStoreDelegate == null ? false : localStoreDelegate.contains(cert);
    }	
    
	/**
	 * {@inheritDoc}
	 */
    public void add(X509Certificate cert)
    {
    	if (localStoreDelegate != null)
    		localStoreDelegate.add(cert);
    }    
	
	/**
	 * {@inheritDoc}
	 */
    public void remove(X509Certificate cert)
    {
    	if (localStoreDelegate != null)
    		localStoreDelegate.remove(cert);
    }    
    
    
	/**
	 * {@inheritDoc}
	 */  
    @SuppressWarnings("unchecked")
    @Override
    public Collection<X509Certificate> getCertificates(String subjectName)
    {
    	LOGGER.debug("\nIn DNSCertificateStore.getCertificates for subjectName: '" + subjectName + "'\n");
    	
      	String realSubjectName;
    	int index;
		if ((index = subjectName.indexOf("EMAILADDRESS=")) > -1)
			realSubjectName = subjectName.substring(index + "EMAILADDRESS=".length());
		else
			realSubjectName = subjectName;    	
    	
    	Collection<X509Certificate> retVal;
    	
    	JCS cache = getCache();
    	
     	if (cache != null)
    	{
    		retVal = (Collection<X509Certificate>)cache.get(realSubjectName);
    		if (retVal == null || retVal.size() == 0)
    		{
    			retVal = this.lookupDNS(realSubjectName);
    			if (retVal == null || retVal.size() == 0)
    			{
    				LOGGER.info("getCertificates(String subjectName) - Could not find a DNS certificate for subject " + subjectName);
    			}
    		}
    	}
    	else // cache miss
    	{
     		retVal = this.lookupDNS(realSubjectName);
    		if (retVal.size() == 0)
    		{
    			if (localStoreDelegate != null)
    			{
	    			retVal = localStoreDelegate.getCertificates(realSubjectName); // last ditch effort is to go to the bootstrap cache
	    			if (retVal == null || retVal.size() == 0)
	    			{
	    				LOGGER.info("getCertificates(String subjectName) - Could not find a DNS certificate for subject " + subjectName);
	    			}
    			}
    			else 
    				LOGGER.info("getCertificates(String subjectName) - Could not find a DNS certificate for subject " + subjectName);
    		} 
    	}
     	     	
		// If we did not find a cert via DNS, try searching for it via LDAP
		if ((retVal == null) || 
				(retVal != null && retVal.size() == 0)) {
					
			LOGGER.debug("\nDid not find certs via DNS, try looking in LDAP...\n");
			retVal = lookupLDAP(realSubjectName);
			
			//-----------------------------------------------------------------------------------------
			// If you don't find any cert records the first time via LDAP, try searching with only the 
			// "domain" part of the email.
			//-----------------------------------------------------------------------------------------		
			if ((retVal == null) || (retVal.size() == 0)) {
				String domainName = getDomainNameFromEmail(realSubjectName);
				
				if (domainName.length() < realSubjectName.length()) {
					retVal = lookupLDAP(domainName);
				}
			} 
		}  	
    	
    	return retVal;
    }    
    
    
    
	/**
	 * Gets a "domain" name from the passed in "email" name.
	 * 
	 * @param emailName
	 * 		Contains an email name from which to extract the "domain" name.
	 * @return
	 * 		Returns the domain part of the passed in email name.
	 */
	private String getDomainNameFromEmail(String emailName) {		
		String domainName = "";
		
		if (emailName != null) {
			int index = emailName.indexOf("@");
			
			if (index != -1) {
				domainName = emailName.substring(index + 1);
			} else {
				domainName = emailName;
			}			
		}
		
		return domainName;
	}


	/**
	 * {@inheritDoc}
	 */
    @Override
    public Collection<X509Certificate> getAllCertificates()
    {
    	return (localStoreDelegate == null) ? null : localStoreDelegate.getAllCertificates(); 
    }    
    
	private Collection<X509Certificate> lookupDNS(String name)
	{
		String domain;
		String lookupName = name.replace('@', '.');
		Collection<X509Certificate> retVal = new ArrayList<X509Certificate>();
				
		// get the domain of the address
		int index;
		if ((index = name.indexOf("@")) > -1)
			domain = name.substring(index + 1);
		else
			domain = name;
		
		try
		{			
			// try the configured servers first
			Lookup lu = new Lookup(new Name(lookupName), Type.CERT);
			lu.setResolver(createExResolver(servers.toArray(new String[servers.size()]), retries, timeout)); // default retries is 3, limite to 2
			
			LOGGER.debug("\nIn lookupDNS - using name: '" + lookupName + "' to find a CERT record... \n");
			
			Record[] retRecords = lu.run();
			
			if (retRecords == null || retRecords.length == 0)
			{
				Name tempDomain;
				
				// try to find the resource's name server records
				// the address may be an alias so check if there is a CNAME record
				lu = new Lookup(new Name(lookupName), Type.CNAME);
				lu.setResolver(createExResolver(servers.toArray(new String[servers.size()]), retries, timeout));
				
				retRecords = lu.run();	
				if (retRecords != null && retRecords.length > 0)
				{
					CNAMERecord cnameRect = (CNAMERecord)retRecords[0];
					tempDomain = cnameRect.getTarget();
				}
				else {
					tempDomain = new Name(domain);  // not a CNAME	
				}
					
				// look for a name server records
				while (tempDomain.labels() > 1)
				{
					lu = new Lookup(tempDomain, Type.NS);
					lu.setResolver(createExResolver(servers.toArray(new String[servers.size()]), retries, timeout));
					retRecords = lu.run();
					
					if (retRecords != null && retRecords.length > 0)
						break;
					
					tempDomain = new Name(tempDomain.toString().substring((tempDomain.toString().indexOf(".") + 1)));
				}
				
				if (retRecords == null || retRecords.length == 0) {		
					LOGGER.debug("\nIn lookupDNS - cannot find a NAME server, bailing out. \n");
					return retVal; // can't find a name server... bail
				}
				
				String[] remoteServers = new String[retRecords.length];
				for (int i = 0; i < remoteServers.length - 0; ++i)
				{
					remoteServers[i] = ((NSRecord)retRecords[i]).getTarget().toString();
				}
				
				// search the name servers for the cert
				lu = new Lookup(new Name(lookupName), Type.CERT);
				lu.setResolver(createExResolver(remoteServers, 2, 3));
				
				retRecords = lu.run();
			}
						
			if (retRecords != null)
			{
				retVal = new ArrayList<X509Certificate>();
				for (Record rec : retRecords)
				{
					if (rec instanceof CERTRecord) 
					{
						CERTRecord certRec = (CERTRecord)rec;
						switch(certRec.getCertType())
						{
							case CERTRecord.PKIX:
							{
								Certificate certToAdd = convertPXIXRecordToCert(certRec);//CERTConverter.parseRecord((CERTRecord)rec);
								if (certToAdd != null && certToAdd instanceof X509Certificate) {// may not be an X509Cert
									LOGGER.debug("\nIn lookupDNS - FOUND cert record and converted from PKIX to CERT \n");
									retVal.add((X509Certificate)certToAdd);
								}
								break;
							}
							case CERTRecord.URI:
							{
								//TODO: Implement
							}
							default:
							{
								LOGGER.warn("Unknown CERT type " + certRec.getCertType() + " encountered for lookup name" + lookupName);
							}
						}
					}
				}			
			}
			else if (domain.length() < name.length())  // if this is an email address, do the search again and the host level
				retVal = lookupDNS(domain);			
		}
		catch (Exception e)
		{
			e.printStackTrace();
			throw new NHINDException(e);
		}
		
		
		// add or update the local cert store
		if (retVal != null && retVal.size() > 0 && localStoreDelegate != null)
		{
			for (X509Certificate cert : retVal)
			{

				if (localStoreDelegate != null)
				{
					if (localStoreDelegate.contains(cert)) 
						localStoreDelegate.update(cert);
					else
						localStoreDelegate.add(cert);
				}
			}			
			try
			{
				if (cache != null)
					cache.put(name, retVal);
			}
			catch (CacheException e)
			{
				/*
				 * TODO: handle exception
				 */
			}
		}
		return retVal;
	}



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
	private Collection<X509Certificate> lookupLDAP(String directName) {		
		Collection<X509Certificate> resultLdapCerts = new ArrayList<X509Certificate>();
		
		LOGGER.debug("\nBegin lookupLDAP - directName: '" + directName + "' \n");
		
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
						return -1;
					} else if (o1.getWeight() > o2.getWeight()) {
						return 1;
					} else {
						return 0;
					}
				}
			}
		}
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



	/**
	 * Sort the passed in "SRVRecord" objects. The sorting is based first on "priority" and then on "weight".
	 * 
	 * @param srvRecords
	 * 		Contains the list of "SRVRecord" objects to sort.
	 * @return
	 * 		Returns a list of sorted "SRVRecord" objects.
	 */
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


	public void flush(boolean purgeBootStrap) 
	{
		
		if (cache != null)
		{
			try
			{
				cache.clear();
			}
			catch (CacheException e)
			{
				/**
				 * TODO: handle exception
				 */
			}
		
			if (purgeBootStrap && this.localStoreDelegate != null)
			{
				localStoreDelegate.remove(localStoreDelegate.getAllCertificates());
			}
		}
	}

	@SuppressWarnings("unused")
	public void loadBootStrap() 
	{
		if (localStoreDelegate == null)
			throw new IllegalStateException("The boot strap store has not been set.");
		

		JCS cache = null;
		if ((cache = getCache()) != null)
		{
			Map<String, Collection<X509Certificate>> cacheBuilderMap = new HashMap<String, Collection<X509Certificate>>();
			for (X509Certificate cert : localStoreDelegate.getAllCertificates())
			{
				/*
				 * TODO: need to decide how the entries/subjects will be indexed and named
				 */
			}
			
			for (Entry<String, Collection<X509Certificate>> entry : cacheBuilderMap.entrySet())
			{
				try
				{
					cache.put(entry.getKey(), entry.getValue());
				}
				catch (CacheException e)
				{
					/*
					 * TODO: handle exception
					 */
				}
			}
		}
	}

	public void loadBootStrap(CertificateStore bootstrapStore) 
	{
		if (localStoreDelegate == null)
		{
			throw new IllegalArgumentException();
		}
		this.localStoreDelegate = bootstrapStore;
		loadBootStrap();
	}

	public void setBootStrap(CertificateStore bootstrapStore) 
	{
		if (localStoreDelegate == null)
		{
			throw new IllegalArgumentException();
		}
		this.localStoreDelegate = bootstrapStore;		
	}

	public void setCachePolicy(CertStoreCachePolicy policy) 
	{		
		this.cachePolicy = policy;
		applyCachePolicy(policy);
	}
	
	private void applyCachePolicy(CertStoreCachePolicy policy)
	{
		if (getCache() != null)
		{
			try
			{
				ICompositeCacheAttributes attributes = cache.getCacheAttributes();
				attributes.setMaxObjects(policy.getMaxItems());
				attributes.setUseLateral(false);
				attributes.setUseRemote(false);
				cache.setCacheAttributes(attributes);
				
				IElementAttributes eattributes = cache.getDefaultElementAttributes();
				eattributes.setMaxLifeSeconds(policy.getSubjectTTL());
				eattributes.setIsEternal(false);
				eattributes.setIsLateral(false);
				eattributes.setIsRemote(false);		
				
				cache.setDefaultElementAttributes(eattributes);
			}
			catch (CacheException e)
			{
				// TODO: Handle exception
			}
		}
	}
	
	public static class DefaultDNSCachePolicy implements CertStoreCachePolicy
	{
		protected final int maxItems;
		protected final int subjectTTL;
		
		public DefaultDNSCachePolicy()
		{
			OptionsParameter param = OptionsManager.getInstance().getParameter(OptionsParameter.DNS_CERT_RESOLVER_MAX_CACHE_SIZE);
			maxItems =  OptionsParameter.getParamValueAsInteger(param, DEFAULT_DNS_MAX_CAHCE_ITEMS); 
			
			param = OptionsManager.getInstance().getParameter(OptionsParameter.DNS_CERT_RESOLVER_CACHE_TTL);
			subjectTTL =  OptionsParameter.getParamValueAsInteger(param, DEFAULT_DNS_TTL); 
		}
		
		public int getMaxItems() 
		{
			return maxItems;
		}

		public int getSubjectTTL() 
		{
			return subjectTTL;
		}
		
	}
	
	protected ExtendedResolver createExResolver(String[] servers, int retries, int timeout)
	{
		ExtendedResolver retVal = null;
		try
		{
			retVal = new ExtendedResolver(servers);
			retVal.setRetries(retries);
			retVal.setTimeout(timeout);
			retVal.setTCP(useTCP);
		}
		catch (UnknownHostException e) {/* no-op */}
		return retVal;
	}
	
	protected Certificate convertPXIXRecordToCert(CERTRecord certRec)
	{
		Certificate retVal = null;
		ByteArrayInputStream inputStream = null;
		final byte[] certData = certRec.getCert();


		try
		{
			final CertificateFactory cf = CertificateFactory.getInstance("X.509");
			inputStream = new ByteArrayInputStream(certData);
			retVal = (X509Certificate)cf.generateCertificate(inputStream);
		}
		catch (Exception e)
		{
			LOGGER.warn("Failed to convert certificate from DNS byte data.", e);
		}
		finally
		{
			IOUtils.closeQuietly(inputStream);
		}
		
		return retVal;
	}
}
