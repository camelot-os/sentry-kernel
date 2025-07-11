sys_gpio_toggle
"""""""""""""""

**API definition**

   .. code-block:: c
      :caption: C UAPI for gpio_set syscall

      enum Status __sys_gpio_toggle(devh_t device, uint8_t io_identifier);

**Usage**

   Toggling a given I/O of a given device.

   Any I/O (including standalone I/Os such as buttons, leds, external interrupt lines...)
   are always declared as a device in the device tree, which always generate a dedicated
   device handle to which the I/O is associated.
   When the device is a SoC-device that requires I/O configuration, the very same
   mechanisms is used, through the standard definition and usage of pinctrl attribute.

   .. code-block:: dts
       :linenos:

       led0: led_0 {
   		compatible = "gpio-leds";
       	sentry,owner = <0xbabe>;
       	pinctrl-0 = <&led_pc7>;
       	status = "okay";
   	};

   If the I/O exists in the given device and if the device is owned by the application,
   this function set the GPIO value to the value given, while the GPIO is configured in
   output mode.

   .. code-block:: C
      :linenos:
      :caption: toggling I/O 0 (fist element of the pinctrl)

      if (__sys_gpio_toggle(myhandle, 0) != STATUS_OK) {
         // [...]
      }

**Required capability**

   CAPA_DEV_IO is required for autonomous GPIO-based devices. For other devices, each
   device hold its own capability. devices that hold pinmux are motly buses, that
   require the CAPA_DEV_BUSES.

**Return values**

   * STATUS_INVALID if the pin definition do not exist or is in input mode
   * STATUS_OK
