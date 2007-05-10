package net.sourceforge.czt.zml2html.xml;

import java.util.HashMap;
import java.util.NoSuchElementException;

import java.util.Date;
import java.util.Iterator;

/**
 * A Pool of Objects.
 *
 * This class is threadsafe; any subclasses are expected to maintain threadsafety.
 *
 * Objects are stored internally in a HashMap, where they map to a
 * nz.ac.waikato.ga11.xml.PoolObjectMeta instance.
 *
 */
public abstract class ObjectPool extends HashMap
{
    /* If not specified at construction time, this is the initial maxPoolsize value */
    private static final int DEFAULT_MAX_POOLSIZE = 3;

    /* maximum amount of objects in this pool */
    private int maxPoolsize;

    /* identifier for this object pool */
    private String id;

    /**
     * Create a new ObjectPool of size <code>DEFAULT_MAX_POOLSIZE</code>
     *
     */
    public ObjectPool(String id)
    {	
	this(DEFAULT_MAX_POOLSIZE, id);
    }

    /**
     * Create a new ObjectPool of size <code>maxPoolsize</code>
     *
     */
    public ObjectPool(int maxPoolsize, String id)
    {
	super(maxPoolsize);
	this.maxPoolsize = maxPoolsize;
	this.id = id;
    }

    /**
     * Informs whether the pool contains <code>maxPoolsize</code> objects.
     *
     * @return <code>true</code> if the pool contains <code>maxPoolsize</code>
     *   objects, else <code>false</code>.
     */
    public boolean isPoolFull()
    {
	return size()==maxPoolsize;
    }


    /**
     * Alter the maximum amount of elements allowed in this pool.
     */
    public void setMaxPoolsize(int maxPoolsize)
    {
	this.maxPoolsize = maxPoolsize;
    }
    
    /** 
     * Retrieves an available instance from the pool. If no instances are
     * available and the pool is not yet full, adds a new instances to
     * the pool and returns it.
     *
     * @throws ResourceUnavailableException if currently no instances are available,
     *  and no new instances can be created because the size of the pool is > MAX_SIZE.
     *
     */
    private Object getInstanceAttempt()
	throws ResourceUnavailableException
    {
	Object poolObject = null;
	try {
	    synchronized(this) {
		poolObject = getAvailablePoolObject();
		return poolObject;
	    }
	} catch (NoSuchElementException nse) {
	    try {
		poolObject = newInstance();
		PoolObjectMeta meta = new PoolObjectMeta();
		put(poolObject, meta);
		return poolObject;
	    } catch (IndexOutOfBoundsException iob) {
		throw new ResourceUnavailableException(iob);
	    } catch (XMLException xmle) {
		throw new ResourceUnavailableException(xmle);
	    }
	}
    }

    /**
     * Delivers a pool object instance.
     *
     * If no instance is available, will try to add a new Object
     * to the pool and deliver it. If the pool is full, will block
     * until an instance can be delivered.
     *
     * @return An object from the pool.
     */
    public synchronized Object getInstance()
    {
	Object poolObject = null;
	while (poolObject == null) {
	    try {
		poolObject = getInstanceAttempt();
		checkout(poolObject);
	    } catch (ResourceUnavailableException rue) {
		try {
		    this.wait();
		} catch(InterruptedException ie) {
		    throw new RuntimeException(ie);
		}
	    }	    	    
	}
	return poolObject;
    }

    /**
     * Creates a new <code>Object</code> instance.
     * 
     * <b>Note:</b> A new Object is returned by this method,
     * but it is not added to the pool.
     */
    protected abstract Object newInstance()
	throws IndexOutOfBoundsException, XMLException;

    /**
     * Attempts to obtain an available instance from the Object Pool.
     *
     * @returns An available object from the pool.
     *
     * @throws NoSuchElementException If there is no available instance in the pool.
     */ 
    private synchronized Object getAvailablePoolObject()
	throws NoSuchElementException
    {
	Iterator poolObjects = keySet().iterator();
	while (poolObjects.hasNext()) {
	    Object poolObject = poolObjects.next();
	    if (isAvailable(poolObject)) {
		return poolObject;
	    }
	}
	throw new NoSuchElementException();
    }

    /**
     * Indicates whether a given object is available in the Pool.
     *
     * @param poolObject The object for which to check availability
     *
     * @return <code>true</code> if the passed object is available
     *
     * @throws NoSuchElementException if the passed <code>poolObject</code>
     *   does not exist in the Pool.
     *
     */
    public boolean isAvailable(Object poolObject)
	throws NoSuchElementException
    {
	checkPoolForObject(poolObject);

	PoolObjectMeta meta = (PoolObjectMeta)get(poolObject);
	
	if (meta.available) {
	    return true;	    
	}

	return false;
    }

    /**
     * Called by pool clients to indicate they are done with a
     * given object; it is now available to other objects.
     *
     * @param poolObject the object to be released.
     */
    public void release(Object poolObject)
    {
	try {
	    checkPoolForObject(poolObject);
	    getMeta(poolObject).release();
	} catch(NoSuchElementException nse) {
	    // do nothing; the object was not checked out
	}
    }

    /**
     * Returns the PoolObjectMeta metadata instance associated with each pool entry.
     *
     * @param poolObject the <code>Object</code> for which to obtain metadata.
     *
     */
    private PoolObjectMeta getMeta(Object poolObject)
    {
	return (PoolObjectMeta)get(poolObject);
    }

    /**
     * Safety valve function that checks whether a given object is contained in the pool.
     *
     * @param poolObject Object to look for in the pool.
     * 
     * @throws NoSuchElementException if <code>poolObject</code> is not contained
     *   in the pool.
     *
     */
    private void checkPoolForObject(Object poolObject)
	throws NoSuchElementException
    {
	if (!containsKey(poolObject))
	    throw new NoSuchElementException("Pool "+id+" does not contain object "+poolObject);
    }

    /**
     * Determines whether the ObjectPool is filled up.
     *
     * @return <code>true</code> if the Pool contains <code>maxPoolsize</code>
     *   entries, else false.
     *
     */
    public boolean isFull()
    {
	return size() >= maxPoolsize;
    }

    /**
     * Safety valve function.
     *
     */
    public void bailIfFull()
	throws IndexOutOfBoundsException
    {
	if (isFull())
	    throw new IndexOutOfBoundsException("Pool "+id+" is full at instance count "+maxPoolsize);
    }

    /**
     * Returns the public ID of this pool
     *
     * @return the public ID of this pool
     */
    public String getId()
    {
	return this.id;
    }

    /**
     * marks the passed <code>poolObject</code> as
     * checked out.
     */
    private void checkout(Object poolObject)
	throws ResourceUnavailableException
    {
	getMeta(poolObject).checkout();
    }

    /**
     * Class to describe the status of a pool object.
     *
     */
    protected class PoolObjectMeta
    {
	public synchronized void checkout()
	    throws ResourceUnavailableException
	{
	    if (available != true)
		throw new ResourceUnavailableException("Resource is not available");
	    available=false;
	    checkoutCount++;
	}

	public synchronized void release()
	{
	    this.available = true;
	    this.notifyAll();
	}

	public Date creationDate = new Date();
	public int checkoutCount = 0;
	public boolean available = true;

	public PoolObjectMeta() {}	
    }
}
