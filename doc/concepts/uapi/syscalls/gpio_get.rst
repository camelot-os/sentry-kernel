sys_gpio_get
""""""""""""

**API definition**

   .. code-block:: c
      :caption: C UAPI for gpio_get syscall

      enum Status __sys_gpio_get(devh_t device, uint8_t io_identifier);

**Usage**

   Getting a given I/O of a given device.

   Any I/O (including standalone I/Os such as buttons, leds, external interrupt lines...)
   are always declared as a device in the device tree, which always generate a dedicated
   device handle to which the I/O is associated.
   When the device is a SoC-device that requires I/O configuration, the very same
   mechanisms is used, through the standard definition and usage of pinctrl attribute.

   .. code-block:: dts
       :linenos:

       button0: button_0 {
   		compatible = "gpio-button";
       	sentry,owner = <0xbabe>;
       	pinctrl-0 = <&button_pa4>;
       	status = "okay";
   	};

   If the I/O exists in the given device and if the device is owned by the application,
   this function get back the current GPIO value into the svc_exchange area.
   The GPIO value is written into the fist byte of the svc_echange.

   .. code-block:: C
      :linenos:
      :caption: getting I/O 0 from button

      if (__sys_gpio_get(myhandle, 0) != STATUS_OK) {
         // [...]
      }
      copy_from_kernel(uint8_t *button_value, sizeof(uint8_t));

**Required capability**

   CAPA_DEV_IO is required for autonomous GPIO-based devices. For other devices, each
   device hold its own capability. devices that hold pinmux are motly buses, that
   require the CAPA_DEV_BUSES.

**Return values**

   * STATUS_INVALID if the pin definition do not exist
   * STATUS_OK
